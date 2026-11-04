module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Existence and uniqueness of the topology on the points of an algebraic space (Stacks 03BX)

Tag 03BX asserts that there is a *unique* way to topologize the point sets of all the
algebraic spaces over a scheme `S` so that

1. on a scheme the topology is the usual one, under the canonical bijection of points;
2. every morphism of algebraic spaces is continuous on points;
3. an étale morphism from a scheme to an algebraic space is open on points.

`StacksFrontier/AlgebraicGeometry/Spaces/PointsTopology.lean` constructs a topology
`AlgebraicGeometry.Space.pointTopology` directly, as the topology detected by all
scheme-valued points, and proves clauses (1) and (2) for it. This file completes the tag:
clause (3) is proved for that topology, so the three conditions are satisfiable, and then
*every* family satisfying the three conditions is shown to be the constructed one.

Clause (3) is the only place where the fibre products of the site are needed. An étale
morphism of presheaves `f : yoneda.obj U ⟶ F` is in particular relatively representable, so
its base change along an arbitrary scheme-valued point `a : yoneda.obj V ⟶ F` is a morphism
of the site `R ⟶ V`, again étale. Stacks 03H4 says the points of `yoneda.obj R` surject onto
the pairs of points of `yoneda.obj U` and `yoneda.obj V` agreeing in `F`, which turns the
preimage of the image `|f| '' W` into the image of a preimage along the two projections of
`R`. Both of those are maps of *schemes*, where continuity and openness are clauses (1) and
(2) together with the openness of an étale morphism of schemes.

Uniqueness then needs no further geometry. Given a family `t`, clauses (1) and (2) for `t`
and clause (1) for the constructed topology identify the two on a represented presheaf; for
a general algebraic space `F` choose a surjective étale atlas `p : yoneda.obj U ⟶ F`, which
is surjective on points by Stacks 03H5, and clauses (2) and (3) exhibit `|p|` as an open
continuous surjection — hence a quotient map — for both topologies at once. Two topologies
coinduced by the same map from the same topology are equal.

## Main definitions

* `AlgebraicGeometry.Space.PointTopologyFamily` is a family of topologies on the points of
  the algebraic spaces over `S` satisfying the three conditions of Tag 03BX.
* `AlgebraicGeometry.Space.pointTopologyFamily` is the family built from
  `AlgebraicGeometry.Space.pointTopology`.
* `AlgebraicGeometry.Space.chosenPointTopologyFamily` is the family obtained from the
  existence statement by `Classical.choose`.

## Main results

* `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_etale` is clause (3) of Tag 03BX for the
  constructed topology.
* `AlgebraicGeometry.Space.PointTopologyFamily.topology_yoneda`: on a represented presheaf
  every family agrees with `AlgebraicGeometry.Space.pointTopology`, because clause (1) pins
  the topology down there.
* `AlgebraicGeometry.Space.PointTopologyFamily.topology_eq`: every family satisfying the
  three conditions assigns to each algebraic space the constructed topology
  `AlgebraicGeometry.Space.pointTopology`. This is the identification that lets a statement
  written against an abstractly chosen topology be read against the constructed one.
* `AlgebraicGeometry.Space.existsUnique_pointTopologyFamily`: **Stacks 03BX**.
* `AlgebraicGeometry.Space.chosenPointTopologyFamily_topology_eq`: the same identification
  for the family produced by `Classical.choose`.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` takes no algebraicity hypothesis, while a family of
Tag 03BX is indexed by an algebraic space together with its proof of algebraicity. The
`topology` field of `AlgebraicGeometry.Space.pointTopologyFamily` therefore discards its
second argument, which is why `PointTopologyFamily.topology_eq` can be stated as an equality
of topologies rather than of families, and why it specializes to `rfl` on that family.

Uniqueness is recorded both as the `∃!` of the tag and, more usably, as
`AlgebraicGeometry.Space.PointTopologyFamily.eq`.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The point topology of a represented presheaf -/

/-- A set of points of a represented presheaf is scheme open exactly when it is the preimage
of an open subset of the representing scheme under the bijection of points. This repackages
`AlgebraicGeometry.Space.IsSchemeOpen`, whose membership condition is phrased at field-valued
representatives, as a statement about the map
`AlgebraicGeometry.Space.pointsToScheme`. -/
theorem isSchemeOpen_iff_exists_preimage (U : BigFppfOver B S hS)
    (W : Set (points B S hS (yoneda.obj U))) :
    IsSchemeOpen B S hS U W ↔
      ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U),
        IsOpen V ∧ pointsToScheme B S hS U ⁻¹' V = W := by
  constructor
  · rintro ⟨V, hV, hmem⟩
    refine ⟨V, hV, ?_⟩
    ext x
    induction x using Quot.inductionOn with
    | h p => exact (hmem p).symm
  · rintro ⟨V, hV, rfl⟩
    exact ⟨V, hV, fun _ ↦ Iff.rfl⟩

/-- An étale morphism of the big fppf site over `S` is open on the points of the represented
presheaves: by clause (1) of Tag 03BX the point topology of a represented presheaf is the
topology of the representing scheme, and an étale morphism of schemes is open. -/
theorem isOpenMap_pointsMap_yonedaMap_of_etale {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : Etale ((BigFppfOver.toScheme B S hS).map h)) :
    @IsOpenMap _ _ (pointTopology B S hS (yoneda.obj U))
      (pointTopology B S hS (yoneda.obj V))
      (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) := by
  intro W hW
  rw [isOpen_yoneda_iff_isSchemeOpen, isSchemeOpen_iff_exists_preimage] at hW
  obtain ⟨V₀, hV₀, rfl⟩ := hW
  rw [isOpen_yoneda_iff_isSchemeOpen, isSchemeOpen_iff_exists_preimage]
  refine ⟨(BigFppfOver.toScheme B S hS).map h '' V₀,
    ((BigFppfOver.toScheme B S hS).map h).isOpenMap V₀ hV₀, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨v, hv, hvy⟩
    obtain ⟨x, hx⟩ := surjective_pointsToScheme B S hS U v
    exact ⟨x, by rwa [hx], injective_pointsToScheme B S hS V
      (by rw [pointsToScheme_pointsMap, hx, hvy])⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨pointsToScheme B S hS U x, hx, by rw [← pointsToScheme_pointsMap, hxy]⟩

/-! ### Clause (3) for the constructed topology -/

/-- The fibre product of an arbitrary scheme-valued point with an étale morphism from a
represented presheaf is represented, and its projection to the first factor is étale. This is
relative representability of an étale morphism of presheaves, together with the defining
property that its represented base changes are étale. -/
private theorem exists_etalePullback {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : BigFppfOver B S hS} {f : yoneda.obj U ⟶ F}
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) (a : yoneda.obj V ⟶ F) :
    ∃ (R : BigFppfOver B S hS) (toU : R ⟶ U) (toV : R ⟶ V),
      IsPullback (yoneda.map toU) (yoneda.map toV) f a ∧
        Etale ((BigFppfOver.toScheme B S hS).map toV) := by
  obtain ⟨R, toV, fst, hpb⟩ := hf.1 a
  refine ⟨R, yoneda.preimage fst, toV, ?_, hf.2 a fst toV hpb⟩
  rwa [yoneda.map_preimage]

/-- **Stacks 03BX, clause (3).** An étale morphism from a represented presheaf to an algebraic
space is open on points, for the constructed topology
`AlgebraicGeometry.Space.pointTopology`. -/
theorem isOpenMap_pointsMap_of_etale {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    @IsOpenMap _ _ (pointTopology B S hS (yoneda.obj U)) (pointTopology B S hS F)
      (pointsMap B S hS (yoneda.obj U) f) := by
  intro W hW
  rw [isOpen_pointTopology_iff]
  intro V a
  obtain ⟨R, toU, toV, hpb, htoV⟩ := exists_etalePullback B S hS hf a
  let RA : AlgebraicSpaces B S hS := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩
  let UA : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let VA : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let FA : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let projU : RA ⟶ UA := ObjectProperty.homMk (yoneda.map toU)
  let projV : RA ⟶ VA := ObjectProperty.homMk (yoneda.map toV)
  let fA : UA ⟶ FA := ObjectProperty.homMk f
  let aA : VA ⟶ FA := ObjectProperty.homMk a
  have hsq : IsPullback projU projV fA aA :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (algebraicSpaceProperty B S hS)) hpb
  have hlift : ∀ (x : points B S hS (yoneda.obj U)) (y : points B S hS (yoneda.obj V)),
      pointsMap B S hS (yoneda.obj U) f x = pointsMap B S hS (yoneda.obj V) a y →
      ∃ r : points B S hS (yoneda.obj R),
        pointsMap B S hS (yoneda.obj R) (yoneda.map toU) r = x ∧
          pointsMap B S hS (yoneda.obj R) (yoneda.map toV) r = y :=
    fun x y hxy ↦ exists_point_of_isPullback B S hS hsq x y hxy
  have hset : pointsMap B S hS (yoneda.obj V) a ⁻¹'
        (pointsMap B S hS (yoneda.obj U) f '' W) =
      pointsMap B S hS (yoneda.obj R) (yoneda.map toV) ''
        (pointsMap B S hS (yoneda.obj R) (yoneda.map toU) ⁻¹' W) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨r, hrU, hrV⟩ := hlift x y hxy
      exact ⟨r, by rwa [hrU], hrV⟩
    · rintro ⟨r, hr, hrV⟩
      refine ⟨pointsMap B S hS (yoneda.obj R) (yoneda.map toU) r, hr, ?_⟩
      have hw := congrArg (fun k ↦ pointsMap B S hS (yoneda.obj R) k r) hpb.w
      simp only [pointsMap_comp, Function.comp_apply] at hw
      rw [← hrV, ← hw]
  have hpre : @IsOpen _ (pointTopology B S hS (yoneda.obj R))
      (pointsMap B S hS (yoneda.obj R) (yoneda.map toU) ⁻¹' W) := by
    let _tR : TopologicalSpace (points B S hS (yoneda.obj R)) :=
      pointTopology B S hS (yoneda.obj R)
    let _tU : TopologicalSpace (points B S hS (yoneda.obj U)) :=
      pointTopology B S hS (yoneda.obj U)
    exact hW.preimage (continuous_pointsMap B S hS (yoneda.map toU))
  rw [hset, ← isOpen_yoneda_iff_isSchemeOpen]
  exact isOpenMap_pointsMap_yonedaMap_of_etale B S hS toV htoV _ hpre

/-! ### The family of topologies characterised by Tag 03BX -/

/-- A family of topologies on the points of the algebraic spaces over `S` satisfying the three
conditions of Tag 03BX: it is the scheme topology on a scheme, every morphism of algebraic
spaces is continuous on points, and an étale morphism from a scheme is open on points. -/
structure PointTopologyFamily where
  /-- The topology assigned to each algebraic space. -/
  topology : ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
    IsAlgebraicSpace B S hS F → TopologicalSpace (points B S hS F)
  /-- For a scheme, the open sets are exactly those cut out by an open subset of the scheme
  under the canonical identification of points. -/
  scheme : ∀ (U : BigFppfOver B S hS) (W : Set (points B S hS (yoneda.obj U))),
    @IsOpen _ (topology (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) W ↔
      ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U),
        IsOpen V ∧
          ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
            (p.class B S hS (yoneda.obj U) ∈ W ↔ schemePoint B S hS U p ∈ V)
  /-- Every morphism of algebraic spaces is continuous on points. -/
  continuous : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G),
    @Continuous _ _ (topology F hF) (topology G hG) (pointsMap B S hS F f)
  /-- An étale morphism from a scheme to an algebraic space is open on points. -/
  etale_isOpenMap : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (hF : IsAlgebraicSpace B S hS F) (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f →
    @IsOpenMap _ _ (topology (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
      (topology F hF) (pointsMap B S hS (yoneda.obj U) f)

/-- The constructed topology `AlgebraicGeometry.Space.pointTopology` satisfies the three
conditions of Tag 03BX: clause (1) is
`AlgebraicGeometry.Space.isOpen_yoneda_iff_isSchemeOpen`, clause (2) is
`AlgebraicGeometry.Space.continuous_pointsMap`, and clause (3) is
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_etale`. -/
def pointTopologyFamily : PointTopologyFamily B S hS where
  topology F _ := pointTopology B S hS F
  scheme U W := isOpen_yoneda_iff_isSchemeOpen B S hS U W
  continuous _ _ f := continuous_pointsMap B S hS f
  etale_isOpenMap hF U f hf := isOpenMap_pointsMap_of_etale B S hS hF U f hf

/-- The topology that `AlgebraicGeometry.Space.pointTopologyFamily` assigns to an algebraic
space is `AlgebraicGeometry.Space.pointTopology`. -/
theorem pointTopologyFamily_topology (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    (pointTopologyFamily B S hS).topology F hF = pointTopology B S hS F := rfl

/-- On a represented presheaf, clause (1) pins any family of point topologies down to
`AlgebraicGeometry.Space.pointTopology`: both have exactly the scheme-open sets. -/
theorem PointTopologyFamily.topology_yoneda (t : PointTopologyFamily B S hS)
    (U : BigFppfOver B S hS) :
    t.topology (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) =
      pointTopology B S hS (yoneda.obj U) := by
  ext W
  exact (t.scheme U W).trans (isOpen_yoneda_iff_isSchemeOpen B S hS U W).symm

/-- **Uniqueness in Tag 03BX, in the form a consumer needs it.** Every family of topologies
satisfying the three conditions assigns to an algebraic space the constructed topology
`AlgebraicGeometry.Space.pointTopology`.

On a represented presheaf this is clause (1) for both topologies. In general a surjective
étale atlas `p : yoneda.obj U ⟶ F` is surjective on points by Stacks 03H5, and clauses (2)
and (3) make `|p|` an open continuous surjection, hence a quotient map, for either topology;
so both are coinduced along `|p|` from the same topology on `|U|`. -/
theorem PointTopologyFamily.topology_eq (t : PointTopologyFamily B S hS)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    t.topology F hF = pointTopology B S hS F := by
  obtain ⟨U, p, hpSurj, hpEtale⟩ := hF.exists_atlas
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) p) :=
    (surjective_iff_surjective_pointsMap B S hS F hF U p).mp hpSurj
  have key : ∀ (tU : TopologicalSpace (points B S hS (yoneda.obj U)))
      (tF : TopologicalSpace (points B S hS F)),
      @IsOpenMap _ _ tU tF (pointsMap B S hS (yoneda.obj U) p) →
      @Continuous _ _ tU tF (pointsMap B S hS (yoneda.obj U) p) →
      tF = TopologicalSpace.coinduced (pointsMap B S hS (yoneda.obj U) p) tU :=
    fun _ _ ho hc ↦ (ho.isQuotientMap hc hsurj).eq_coinduced
  rw [key _ _ (t.etale_isOpenMap hF U p hpEtale)
      (t.continuous (isAlgebraicSpace_yoneda B S hS U) hF p),
    key _ _ (isOpenMap_pointsMap_of_etale B S hS hF U p hpEtale) (continuous_pointsMap B S hS p),
    PointTopologyFamily.topology_yoneda B S hS t U]

/-- **Stacks 03BX.** There is a unique family of topologies on the points of the algebraic
spaces over `S` which is the scheme topology on a scheme, makes every morphism of algebraic
spaces continuous on points, and makes an étale morphism from a scheme open on points. -/
@[stacks 03BX]
theorem existsUnique_pointTopologyFamily :
    ∃! _t : PointTopologyFamily B S hS, True := by
  refine ⟨pointTopologyFamily B S hS, trivial, ?_⟩
  rintro ⟨topology, scheme, continuous, etale_isOpenMap⟩ -
  have htop : topology = (pointTopologyFamily B S hS).topology := by
    funext F hF
    exact PointTopologyFamily.topology_eq B S hS
      ⟨topology, scheme, continuous, etale_isOpenMap⟩ F hF
  subst htop
  rfl

/-- Uniqueness in Tag 03BX: there is at most one family of topologies satisfying the three
conditions. -/
theorem PointTopologyFamily.eq (t t' : PointTopologyFamily B S hS) : t = t' :=
  ((existsUnique_pointTopologyFamily B S hS).unique trivial trivial :)

/-- The family of topologies of Tag 03BX, obtained from the existence statement by
`Classical.choose`. By `AlgebraicGeometry.Space.PointTopologyFamily.eq` it equals
`AlgebraicGeometry.Space.pointTopologyFamily`. -/
noncomputable def chosenPointTopologyFamily : PointTopologyFamily B S hS :=
  Classical.choose (existsUnique_pointTopologyFamily B S hS)

/-- **The identification.** The topology that Tag 03BX's existence statement chooses on the
points of an algebraic space is the constructed topology
`AlgebraicGeometry.Space.pointTopology`, so a statement made against the chosen topology is
a statement about the constructed one. -/
theorem chosenPointTopologyFamily_topology_eq
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    (chosenPointTopologyFamily B S hS).topology F hF = pointTopology B S hS F :=
  PointTopologyFamily.topology_eq B S hS _ F hF

end AlgebraicGeometry.Space

end
