module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantGroupSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison

/-!
# Constant sheaves on the big and small étale sites of a scheme

Let `B` be a big étale site containing a scheme `S` and let `G` be an abstract group. On the
big étale site of `S` and on its small étale site, both the sheafification of the constant
presheaf with value `G` for the site's own topology and its sheafification for the Zariski
topology restricted from schemes have the locally constant `G`-valued maps as their sections.
In particular the two sheafifications agree. The constant sheaf of groups is in both cases the
group-valued functor of points of the constant group scheme `G_S`.

## Main results

* `AlgebraicGeometry.bigEtaleOver_openCoverData`, `smallEtale_openCoverData`,
  `bigEtaleZariski_openCoverData` and `smallEtaleZariski_openCoverData` realise an arbitrary
  open cover of the scheme underlying a site object by a covering family, for the étale and
  for the restricted Zariski topology respectively.
* `AlgebraicGeometry.constantSheafIsoLocallyConstantMaps_bigEtale`,
  `constantSheafIsoLocallyConstantMaps_smallEtale` and the two
  `zariskiConstantSheafIsoLocallyConstantMaps_*` identify the four constant sheaves, and the
  four `_unit` lemmas fix those identifications on constant sections.
* `AlgebraicGeometry.constantGroupSheafRepresentedByConstantGroupScheme_bigEtale`,
  `..._smallEtale`, `zariskiGroupSheafRepresented_bigEtale` and `..._smallEtale` are the
  representations of the constant group sheaves by `G_S`.

## Implementation notes

For the site's own topology an arbitrary open cover has to be replaced by a tautologically
equivalent covering family of the site, which is the content of Stacks 03WW. For the restricted
Zariski topology no such replacement is needed: the open subschemes of a site object are
themselves small enough and étale over `S`, so the open cover is realised in the site directly.

The sheaf condition for the restricted Zariski topology comes from the continuity of the
functor to schemes, which needs it to preserve and create pullbacks; that in turn needs the
size bound and the étale-over property to be closed under limits of cospans.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- Sheafification of presheaves of types in a universe at least that of the objects of a site
whose morphisms live one universe below. Instance search reaches Mathlib's `Type (max u v)`
instance first, whose universe unification fails as a hard error, so the general instance is
supplied directly. -/
theorem hasSheafify_type_max {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    HasSheafify J (Type (max (u + 1) v)) :=
  HasSheafify.mk' J _ (plusPlusAdjunction J _)

attribute [local instance high] hasSheafify_type_max

/-! ### Covering data for the étale topology -/

/-- Precomposing an open cover with the projection from the `ULift` of its index type is still an
open cover. -/
private theorem isOpenCover_comp_ulift_down {X : Scheme.{u}} {U : X → X.Opens}
    (hU : TopologicalSpace.IsOpenCover U) :
    TopologicalSpace.IsOpenCover (fun i : ULift.{u + 1, u} X => U i.down) := by
  rw [TopologicalSpace.IsOpenCover] at hU ⊢
  simpa using hU

/-- The inclusion of a member of the open cover built from `U ∘ ULift.down` lands in `U`. -/
private theorem openCoverOfIsOpenCover_f_mem {X : Scheme.{u}} {U : X → X.Opens}
    (hU : TopologicalSpace.IsOpenCover (fun i : ULift.{u + 1, u} X => U i.down))
    (i : ULift.{u + 1, u} X) (y : (X.openCoverOfIsOpenCover _ hU).X i) :
    (X.openCoverOfIsOpenCover _ hU).f i y ∈ U i.down :=
  y.2

/-- Every open cover of the scheme underlying an object of the big étale site of `S` is
refined by a covering family of that site. -/
public theorem bigEtaleOver_openCoverData (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : BigEtaleOver B S hS}
      (U : (BigEtaleOver.toScheme B S hS).obj T →
        ((BigEtaleOver.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigEtaleOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigEtaleOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈ BigEtaleOver.topology B S hS T ∧
          ∀ i y, (BigEtaleOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let X := B.inclusion.obj T.left
  change TopologicalSpace.IsOpenCover (X := X) U at hU
  have hU' := isOpenCover_comp_ulift_down hU
  let O : X.OpenCover.{u + 1} := X.openCoverOfIsOpenCover _ hU'
  obtain ⟨V, hV, hEq⟩ :=
    BigEtaleSite.exists_isCovering_tautologicallyEquivalent_openCover B T.left O
  rcases hEq.2 with ⟨β, hβ⟩
  choose e he using hβ
  let W : V.I₀ → BigEtaleOver B S hS := fun i => Over.mk (V.f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (V.f i) (by simp [W])
  let E : PreZeroHypercover T := { I₀ := V.I₀, X := W, f := a }
  have hEV : E.map (Over.forget (B.obj S hS)) = V := by
    refine PreZeroHypercover.ext (x := E.map (Over.forget (B.obj S hS))) (y := V) rfl ?_ ?_
    · exact HEq.rfl
    · exact heq_of_eq (funext fun _ => rfl)
  have hfamily : BigEtaleOver.IsCovering B S hS ⟨T, E⟩ := by
    change B.IsCovering ⟨T.left, E.map (Over.forget (B.obj S hS))⟩
    rwa [hEV]
  have hcover : Sieve.ofArrows W a ∈ BigEtaleOver.topology B S hS T := by
    change Sieve.generate E.presieve₀ ∈ (BigEtaleOver.precoverage B S hS).toGrothendieck T
    exact (BigEtaleOver.precoverage B S hS).generate_mem_toGrothendieck ⟨E, rfl, hfamily⟩
  refine ⟨V.I₀, W, a, fun i => (β i).down, hcover, ?_⟩
  intro i y
  have heval : (B.inclusion.map (V.f i)) y = O.f (β i) ((e i).hom y) := by
    have h := congrArg (fun f => f y) (he i)
    have hh := h.symm
    change (B.inclusion.map (V.f i)) y = O.f (β i) ((e i).hom y) at hh
    exact hh
  have hmap : (BigEtaleOver.toScheme B S hS).map (a i) y = (B.inclusion.map (V.f i)) y := rfl
  rw [hmap, heval]
  exact openCoverOfIsOpenCover_f_mem hU' _ _

/-- Every open cover of the scheme underlying an object of the small étale site of `S` is
refined by a covering family of that site. -/
public theorem smallEtale_openCoverData (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : SmallEtale B S hS}
      (U : (SmallEtale.toScheme B S hS).obj T →
        ((SmallEtale.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → SmallEtale B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (SmallEtale.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈ SmallEtale.topology B S hS T ∧
          ∀ i y, (SmallEtale.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let T' := (SmallEtale.inclusion B S hS).obj T
  let X := B.inclusion.obj T'.left
  change TopologicalSpace.IsOpenCover (X := X) U at hU
  have hU' := isOpenCover_comp_ulift_down hU
  let O : X.OpenCover.{u + 1} := X.openCoverOfIsOpenCover _ hU'
  obtain ⟨V, hV, hEq⟩ :=
    BigEtaleSite.exists_isCovering_tautologicallyEquivalent_openCover B T'.left O
  rcases hEq.2 with ⟨β, hβ⟩
  choose e he using hβ
  have hVopen : ∀ i, IsOpenImmersion (B.inclusion.map (V.f i)) := by
    intro i
    have h : IsOpenImmersion ((e i).hom ≫ O.f (β i)) := by infer_instance
    rwa [he i] at h
  let W' : V.I₀ → BigEtaleOver B S hS := fun i => Over.mk (V.f i ≫ T'.hom)
  let a' : ∀ i, W' i ⟶ T' := fun i => Over.homMk (V.f i) (by simp [W'])
  have hW : ∀ i, BigEtaleOver.IsEtaleOver B S hS (W' i) := by
    intro i
    change Etale (B.inclusion.map (W' i).hom)
    change Etale (B.inclusion.map (V.f i ≫ T'.hom))
    rw [Functor.map_comp]
    let : Etale (B.inclusion.map (V.f i)) := by infer_instance
    let : Etale (B.inclusion.map T'.hom) := T.property
    infer_instance
  let W : V.I₀ → SmallEtale B S hS := fun i => ⟨W' i, hW i⟩
  let a : ∀ i, W i ⟶ T := fun i => (SmallEtale.inclusion B S hS).preimage (a' i)
  let E : PreZeroHypercover T := { I₀ := V.I₀, X := W, f := a }
  have ha : ∀ i, (SmallEtale.inclusion B S hS).map (a i) = a' i := fun i =>
    Functor.map_preimage (SmallEtale.inclusion B S hS) (a' i) (X := W i) (Y := T)
  have hEF : (E.map (SmallEtale.inclusion B S hS)).map (Over.forget (B.obj S hS)) = V := by
    refine PreZeroHypercover.ext (x :=
      (E.map (SmallEtale.inclusion B S hS)).map (Over.forget (B.obj S hS))) (y := V) rfl ?_ ?_
    · exact HEq.rfl
    · apply heq_of_eq
      funext i
      change (Over.forget (B.obj S hS)).map ((SmallEtale.inclusion B S hS).map (a i)) = V.f i
      rw [ha i]
      rfl
  have hfamily : SmallEtale.IsCovering B S hS ⟨T, E⟩ := by
    change BigEtaleOver.IsCovering B S hS ⟨T', E.map (SmallEtale.inclusion B S hS)⟩
    change B.IsCovering ⟨T'.left,
      (E.map (SmallEtale.inclusion B S hS)).map (Over.forget (B.obj S hS))⟩
    rwa [hEF]
  have hcover : Sieve.ofArrows W a ∈ SmallEtale.topology B S hS T := by
    change Sieve.generate E.presieve₀ ∈ (SmallEtale.precoverage B S hS).toGrothendieck T
    exact (SmallEtale.precoverage B S hS).generate_mem_toGrothendieck ⟨E, rfl, hfamily⟩
  refine ⟨V.I₀, W, a, fun i => (β i).down, hcover, ?_⟩
  intro i y
  have hmap : (SmallEtale.toScheme B S hS).map (a i) y = (B.inclusion.map (V.f i)) y := by
    change (BigEtaleOver.toScheme B S hS).map ((SmallEtale.inclusion B S hS).map (a i)) y = _
    rw [ha i]
    rfl
  rw [hmap]
  have heval : (B.inclusion.map (V.f i)) y = O.f (β i) ((e i).hom y) := by
    have h := congrArg (fun f => f y) (he i)
    have hh := h.symm
    change (B.inclusion.map (V.f i)) y = O.f (β i) ((e i).hom y) at hh
    exact hh
  rw [heval]
  exact openCoverOfIsOpenCover_f_mem hU' _ _

/-! ### Covering data for the restricted Zariski topology -/

/-- Every open cover of the scheme underlying an object of the big étale site of `S` is
refined by a family which covers for the Zariski topology restricted from schemes. -/
public theorem bigEtaleZariski_openCoverData (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : BigEtaleOver B S hS}
      (U : (BigEtaleOver.toScheme B S hS).obj T →
        ((BigEtaleOver.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigEtaleOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigEtaleOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈
          (BigEtaleOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology T ∧
          ∀ i y, (BigEtaleOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let F := BigEtaleOver.toScheme B S hS
  let X := F.obj T
  have hU' := isOpenCover_comp_ulift_down hU
  let O : X.OpenCover.{u + 1} := X.openCoverOfIsOpenCover _ hU'
  let V : O.I₀ → B.Scheme := fun i =>
    ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) T.left.2⟩
  let f : ∀ i, V i ⟶ T.left := fun i => ⟨O.f i⟩
  let W : O.I₀ → BigEtaleOver B S hS := fun i => Over.mk (f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (f i) (by simp [W])
  have hpush : (Sieve.ofArrows W a).functorPushforward F = Sieve.ofArrows O.X O.f := by
    rw [Sieve.functorPushforward_ofArrows]
    congr 1
  refine ⟨O.I₀, W, a, fun i => i.down, ?_, ?_⟩
  · apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [hpush]
    exact O.mem_grothendieckTopology
  · intro i y
    exact openCoverOfIsOpenCover_f_mem hU' _ _

/-- Every open cover of the scheme underlying an object of the small étale site of `S` is
refined by a family which covers for the Zariski topology restricted from schemes. -/
public theorem smallEtaleZariski_openCoverData (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : SmallEtale B S hS}
      (U : (SmallEtale.toScheme B S hS).obj T →
        ((SmallEtale.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → SmallEtale B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (SmallEtale.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈
          (SmallEtale.toScheme B S hS).restrictedTopology Scheme.zariskiTopology T ∧
          ∀ i y, (SmallEtale.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let F := SmallEtale.toScheme B S hS
  let T' := (SmallEtale.inclusion B S hS).obj T
  let X := B.inclusion.obj T'.left
  have hU' := isOpenCover_comp_ulift_down hU
  let O : X.OpenCover.{u + 1} := X.openCoverOfIsOpenCover _ hU'
  let V : O.I₀ → B.Scheme := fun i =>
    ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) T'.left.2⟩
  let hOmap : ∀ i, B.inclusion.obj (V i) ⟶ B.inclusion.obj T'.left := fun i => by
    change O.X i ⟶ X
    exact O.f i
  let f : ∀ i, V i ⟶ T'.left := fun i => (B.inclusion).preimage (hOmap i)
  have hfm : ∀ i, B.inclusion.map (f i) = O.f i := fun i =>
    (Functor.map_preimage (B.inclusion) (hOmap i) (X := V i) (Y := T'.left)).trans
      (by simp [hOmap])
  let W' : O.I₀ → BigEtaleOver B S hS := fun i => Over.mk (f i ≫ T'.hom)
  let a' : ∀ i, W' i ⟶ T' := fun i => Over.homMk (f i) (by simp [W'])
  have hW : ∀ i, BigEtaleOver.IsEtaleOver B S hS (W' i) := by
    intro i
    change Etale (B.inclusion.map (W' i).hom)
    change Etale (B.inclusion.map (f i ≫ T'.hom))
    rw [Functor.map_comp]
    let : IsOpenImmersion (B.inclusion.map (f i)) := by
      rw [hfm i]
      infer_instance
    let : Etale (B.inclusion.map (f i)) := by infer_instance
    let : Etale (B.inclusion.map T'.hom) := T.property
    infer_instance
  let W : O.I₀ → SmallEtale B S hS := fun i => ⟨W' i, hW i⟩
  let a : ∀ i, W i ⟶ T := fun i => (SmallEtale.inclusion B S hS).preimage (a' i)
  have ha : ∀ i, (SmallEtale.inclusion B S hS).map (a i) = a' i := fun i =>
    Functor.map_preimage (SmallEtale.inclusion B S hS) (a' i) (X := W i) (Y := T)
  have hpush : (Sieve.ofArrows W a).functorPushforward F = Sieve.ofArrows O.X O.f := by
    rw [Sieve.functorPushforward_ofArrows]
    congr 1
    funext i
    change (BigEtaleOver.toScheme B S hS).map ((SmallEtale.inclusion B S hS).map (a i)) = _
    rw [ha i]
    exact hfm i
  refine ⟨O.I₀, W, a, fun i => i.down, ?_, ?_⟩
  · apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [hpush]
    exact O.mem_grothendieckTopology
  · intro i y
    have hmap : F.map (a i) y = O.f i y := by
      change (BigEtaleOver.toScheme B S hS).map ((SmallEtale.inclusion B S hS).map (a i)) y = _
      rw [ha i]
      exact congrArg (fun g => g y) (hfm i)
    rw [hmap]
    exact openCoverOfIsOpenCover_f_mem hU' _ _

/-- Being étale over `S` inside a big étale site is closed under limits of cospans, because
étale morphisms are stable under composition and base change and are detected after
postcomposition with an étale morphism. -/
public theorem smallEtaleProperty_closedUnderCospans (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (BigEtaleOver.IsEtaleOver B S hS).IsClosedUnderLimitsOfShape Limits.WalkingCospan := by
  have : (schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape Limits.WalkingCospan :=
    schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let P : MorphismProperty B.Scheme := fun {X Y} f => Etale (B.inclusion.map f)
  have : P.IsStableUnderComposition := ⟨by
    intro X Y Z f g hf hg
    change Etale (B.inclusion.map f) at hf
    change Etale (B.inclusion.map g) at hg
    change Etale (B.inclusion.map (f ≫ g))
    rw [Functor.map_comp]
    infer_instance⟩
  have : P.IsStableUnderBaseChange := ⟨by
    intro X Y Y' Z f g f' g' h hg
    change Etale (B.inclusion.map g) at hg
    have h' := Functor.map_isPullback B.inclusion h
    change Etale (B.inclusion.map g')
    exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback h') hg⟩
  have : P.HasOfPostcompProperty P := ⟨by
    intro X Y Z f g hg hfg
    change Etale (B.inclusion.map g) at hg
    change Etale (B.inclusion.map (f ≫ g)) at hfg
    rw [Functor.map_comp] at hfg
    exact Etale.of_comp (B.inclusion.map f) (B.inclusion.map g)⟩
  change (P.overObj (X := B.obj S hS)).IsClosedUnderLimitsOfShape Limits.WalkingCospan
  infer_instance

/-! ### The sheaf condition for locally constant maps -/

/-- Locally constant `G`-valued maps form a sheaf on the big étale site of `S`. -/
public theorem locallyConstantMaps_isSheaf_bigEtale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf (BigEtaleOver.topology B S hS)
      ((BigEtaleOver.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  isSheaf_chosenBigEtale_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
    (locallyConstantMapsOver_isSheaf_fpqc S G)

/-- Locally constant `G`-valued maps form a sheaf on the small étale site of `S`. -/
public theorem locallyConstantMaps_isSheaf_smallEtale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf (SmallEtale.topology B S hS)
      ((SmallEtale.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  isSheaf_chosenSmallEtale_of_isSheaf_fpqc B S hS
    (locallyConstantMapsOver G S ⋙ forget GrpCat) (locallyConstantMapsOver_isSheaf_fpqc S G)

/-- Locally constant `G`-valued maps form a sheaf on the big étale site of `S` for the Zariski
topology restricted from schemes. -/
public theorem locallyConstantMaps_isSheaf_bigEtaleZariski (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf
      ((BigEtaleOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      ((BigEtaleOver.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) := by
  let F := BigEtaleOver.toScheme B S hS
  have : (schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape Limits.WalkingCospan :=
    schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  have : Limits.PreservesLimitsOfShape Limits.WalkingCospan F := inferInstance
  exact locallyConstantMaps_isSheaf_restrictedZariski F inferInstance G

/-- Locally constant `G`-valued maps form a sheaf on the small étale site of `S` for the
Zariski topology restricted from schemes. -/
public theorem locallyConstantMaps_isSheaf_smallEtaleZariski (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf
      ((SmallEtale.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      ((SmallEtale.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) := by
  let F := SmallEtale.toScheme B S hS
  have : (schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape Limits.WalkingCospan :=
    schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  have : (BigEtaleOver.IsEtaleOver B S hS).IsClosedUnderLimitsOfShape
      Limits.WalkingCospan := smallEtaleProperty_closedUnderCospans B S hS
  have : Limits.PreservesLimitsOfShape Limits.WalkingCospan F := inferInstance
  exact locallyConstantMaps_isSheaf_restrictedZariski F inferInstance G

/-! ### The constant sheaves -/

/-- Constant sheaves on the chosen big étale site have locally constant sections. -/
@[stacks 03P5 "big étale site"]
public def constantSheafIsoLocallyConstantMaps_bigEtale (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v))).obj G).obj ≅
    ((BigEtaleOver.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn (BigEtaleOver.toScheme B S hS) G
    (BigEtaleOver.topology B S hS) (bigEtaleOver_openCoverData B S hS)
    (openCoverData_bottom (BigEtaleOver.toScheme B S hS) (BigEtaleOver.topology B S hS)
      (bigEtaleOver_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigEtale B S hS G)

/-- The Zariski sheafification on a chosen big étale site has locally constant sections. -/
@[stacks 03P5 "Zariski sheafification on the big étale site"]
public def zariskiConstantSheafIsoLocallyConstantMaps_bigEtale (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf
      ((BigEtaleOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (Type (max (u + 1) v))).obj G).obj ≅
    ((BigEtaleOver.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn (BigEtaleOver.toScheme B S hS) G
    ((BigEtaleOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (bigEtaleZariski_openCoverData B S hS)
    (openCoverData_bottom (BigEtaleOver.toScheme B S hS)
      ((BigEtaleOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (bigEtaleZariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigEtaleZariski B S hS G)

/-- Constant sheaves on the chosen small étale site have locally constant sections. -/
@[stacks 03P5 "small étale site"]
public def constantSheafIsoLocallyConstantMaps_smallEtale (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf (SmallEtale.topology B S hS) (Type (max (u + 1) v))).obj G).obj ≅
    ((SmallEtale.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn (SmallEtale.toScheme B S hS) G
    (SmallEtale.topology B S hS) (smallEtale_openCoverData B S hS)
    (openCoverData_bottom (SmallEtale.toScheme B S hS) (SmallEtale.topology B S hS)
      (smallEtale_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_smallEtale B S hS G)

/-- The Zariski sheafification on a chosen small étale site has locally constant sections. -/
@[stacks 03P5 "Zariski sheafification on the small étale site"]
public def zariskiConstantSheafIsoLocallyConstantMaps_smallEtale (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf
      ((SmallEtale.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (Type (max (u + 1) v))).obj G).obj ≅
    ((SmallEtale.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn (SmallEtale.toScheme B S hS) G
    ((SmallEtale.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (smallEtaleZariski_openCoverData B S hS)
    (openCoverData_bottom (SmallEtale.toScheme B S hS)
      ((SmallEtale.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (smallEtaleZariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_smallEtaleZariski B S hS G)

/-! ### Compatibility with constant sections -/

/-- The specified-topology identification on the big etale site preserves constant sections. -/
@[stacks 03P5 "tau unit on the big etale site"]
public theorem constantSheafIsoLocallyConstantMaps_bigEtale_unit (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (BigEtaleOver.toScheme B S hS)
      (BigEtaleOver.topology B S hS) G
      (constantSheafIsoLocallyConstantMaps_bigEtale B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit (BigEtaleOver.toScheme B S hS) G
    (BigEtaleOver.topology B S hS) (bigEtaleOver_openCoverData B S hS)
    (openCoverData_bottom (BigEtaleOver.toScheme B S hS) (BigEtaleOver.topology B S hS)
      (bigEtaleOver_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigEtale B S hS G)

/-- The Zariski-topology identification on the big etale site preserves constant sections. -/
@[stacks 03P5 "Zariski unit on the big etale site"]
public theorem zariskiConstantSheafIsoLocallyConstantMaps_bigEtale_unit
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (BigEtaleOver.toScheme B S hS)
      ((BigEtaleOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G
      (zariskiConstantSheafIsoLocallyConstantMaps_bigEtale B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit (BigEtaleOver.toScheme B S hS) G
    ((BigEtaleOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (bigEtaleZariski_openCoverData B S hS)
    (openCoverData_bottom (BigEtaleOver.toScheme B S hS)
      ((BigEtaleOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (bigEtaleZariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigEtaleZariski B S hS G)

/-- The specified-topology identification on the small etale site preserves constant
sections. -/
@[stacks 03P5 "tau unit on the small etale site"]
public theorem constantSheafIsoLocallyConstantMaps_smallEtale_unit (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (SmallEtale.toScheme B S hS)
      (SmallEtale.topology B S hS) G
      (constantSheafIsoLocallyConstantMaps_smallEtale B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit (SmallEtale.toScheme B S hS) G
    (SmallEtale.topology B S hS) (smallEtale_openCoverData B S hS)
    (openCoverData_bottom (SmallEtale.toScheme B S hS) (SmallEtale.topology B S hS)
      (smallEtale_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_smallEtale B S hS G)

/-- The Zariski-topology identification on the small etale site preserves constant
sections. -/
@[stacks 03P5 "Zariski unit on the small etale site"]
public theorem zariskiConstantSheafIsoLocallyConstantMaps_smallEtale_unit
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (SmallEtale.toScheme B S hS)
      ((SmallEtale.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G
      (zariskiConstantSheafIsoLocallyConstantMaps_smallEtale B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit (SmallEtale.toScheme B S hS) G
    ((SmallEtale.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (smallEtaleZariski_openCoverData B S hS)
    (openCoverData_bottom (SmallEtale.toScheme B S hS)
      ((SmallEtale.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (smallEtaleZariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_smallEtaleZariski B S hS G)

/-! ### Representation by the constant group scheme -/

/-- Representation of the constant group sheaf on the chosen big étale site. -/
@[stacks 03P5 "group-valued representation on the big étale site"]
public def constantGroupSheafRepresentedByConstantGroupScheme_bigEtale (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S (Over.post (X := B.obj S hS) B.inclusion)
      (BigEtaleOver.topology B S hS) G := by
  let H := Over.post (X := B.obj S hS) B.inclusion
  let J := BigEtaleOver.topology B S hS
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    isSheaf_chosenBigEtale_of_isSheaf_fpqc B S hS
      (locallyConstantMapsOver G S ⋙ forget GrpCat) (locallyConstantMapsOver_isSheaf_fpqc S G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @bigEtaleOver_openCoverData B S hS
  have hEmpty : ∀ {T}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T := by
    intro T hT
    exact openCoverData_bottom (H ⋙ Over.forget S) J hOpen hT
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen hEmpty hSet

/-- Representation of the constant group sheaf on the chosen small étale site. -/
@[stacks 03P5 "group-valued representation on the small étale site"]
public def constantGroupSheafRepresentedByConstantGroupScheme_smallEtale
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S
      (SmallEtale.inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion)
      (SmallEtale.topology B S hS) G := by
  let H := SmallEtale.inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion
  let J := SmallEtale.topology B S hS
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    isSheaf_chosenSmallEtale_of_isSheaf_fpqc B S hS
      (locallyConstantMapsOver G S ⋙ forget GrpCat) (locallyConstantMapsOver_isSheaf_fpqc S G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @smallEtale_openCoverData B S hS
  have hEmpty : ∀ {T}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T := by
    intro T hT
    exact openCoverData_bottom (H ⋙ Over.forget S) J hOpen hT
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen hEmpty hSet

/-- The Zariski constant group sheaf on the chosen big étale site is represented by `G_S`. -/
@[stacks 03P5 "Zariski group sheaf on the big étale site"]
public def zariskiGroupSheafRepresented_bigEtale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S (Over.post (X := B.obj S hS) B.inclusion)
      ((BigEtaleOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G := by
  let H := Over.post (X := B.obj S hS) B.inclusion
  let F := BigEtaleOver.toScheme B S hS
  let J := F.restrictedTopology Scheme.zariskiTopology
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    (Presheaf.isSheaf_of_iso_iff (relativeLocallyConstantMapsIsoOnScheme S H G)).mpr
      (locallyConstantMaps_isSheaf_bigEtaleZariski B S hS G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @bigEtaleZariski_openCoverData B S hS
  have hEmpty : ∀ {T}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T := by
    intro T hT
    exact openCoverData_bottom (H ⋙ Over.forget S) J hOpen hT
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen hEmpty hSet

/-- The Zariski constant group sheaf on the chosen small étale site is represented by `G_S`. -/
@[stacks 03P5 "Zariski group sheaf on the small étale site"]
public def zariskiGroupSheafRepresented_smallEtale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S
      (SmallEtale.inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion)
      ((SmallEtale.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G := by
  let H := SmallEtale.inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion
  let F := SmallEtale.toScheme B S hS
  let J := F.restrictedTopology Scheme.zariskiTopology
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    (Presheaf.isSheaf_of_iso_iff (relativeLocallyConstantMapsIsoOnScheme S H G)).mpr
      (locallyConstantMaps_isSheaf_smallEtaleZariski B S hS G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @smallEtaleZariski_openCoverData B S hS
  have hEmpty : ∀ {T}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T := by
    intro T hT
    exact openCoverData_bottom (H ⋙ Over.forget S) J hOpen hT
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen hEmpty hSet

end AlgebraicGeometry

end
