module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Point.Map
public import Mathlib.Topology.Sets.Closeds
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineDense
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineDenseSubsite
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCover
public import StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the pro-étale sites

The five pro-étale sites of a scheme all have enough points: the chosen pro-étale site of
schemes, the small pro-étale site, the big pro-étale site over the scheme, the affine objects
of the small site, and the affine objects of the big site over the scheme.

The affine sites are the source of the statement. On the big affine site every covering family
is finite by definition, so Deligne's criterion applies to it directly. The affine objects of
the small site are instead covered by spectra of w-contractible rings, over which every
pro-étale covering is refined by a decomposition into finitely many clopen pieces; the clopen
subsets of such a spectrum form a Boolean site whose points are its topological points, and
Deligne's criterion is applied there. The remaining three sites receive the family through the
dense-subsite inclusions of their affine subsites.

## Main results

* `AlgebraicGeometry.ProEtale.proetale_hasEnoughPoints`: all five pro-étale sites have enough
  points.
* `AlgebraicGeometry.ProEtale.schemeProetale_hasConservativeFamily`,
  `AlgebraicGeometry.ProEtale.smallProetale_hasConservativeFamily`,
  `AlgebraicGeometry.ProEtale.bigProetaleOver_hasConservativeFamily`,
  `AlgebraicGeometry.ProEtale.smallAffineProetale_hasConservativeFamily`,
  `AlgebraicGeometry.ProEtale.bigAffineProetale_hasConservativeFamily`: the five sites one at a
  time.

## Implementation notes

A *point* here is a point of the site, not of the topos and not a pro-object: a fibre functor
to sets whose category of neighbourhoods is cofiltered and which is jointly surjective on
coverings, which is `CategoryTheory.GrothendieckTopology.Point`. *Having enough points* is the
existence of a conservative family of such points,
`CategoryTheory.GrothendieckTopology.HasConservativeFamily`; no smallness of the family is
asked for, matching the source, so this is weaker than Mathlib's
`CategoryTheory.GrothendieckTopology.HasEnoughPoints`, which is what Deligne's criterion
produces for the two sites it applies to.

The big sites are the chosen bounded ones: a pro-étale site of schemes with its bound, its
slice over a scheme contained in it, and the affine objects of that slice. Their points take
values one universe up, since the chosen site has objects in `Type (u + 1)`. The small site is
the unrestricted small pro-étale site of the scheme, with no bound and no choice of ambient
big site, and its affine subsite consists of the objects with affine source; their points take
values in `Type u`.

The clopen subsets of a scheme are used as a site in their own right, via the topology whose
covering sieves are the sieves covering every point. Restriction to a clopen piece of an
affine object of the small site is a morphism of sites in both directions, which is what
transports its points.

## References

* [Stacks Project, Tag 0992](https://stacks.math.columbia.edu/tag/0992)
* [Stacks Project, Tag 098N](https://stacks.math.columbia.edu/tag/098N)
* [Stacks Project, Tag 098W](https://stacks.math.columbia.edu/tag/098W)
* [Stacks Project, Tag 0DW0](https://stacks.math.columbia.edu/tag/0DW0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

attribute [local implicit_reducible] CategoryTheory.MorphismProperty
  AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ProEtale

/-- The topology on the clopen subsets of a topological space whose covering sieves are those
containing, for every point of the target, a member containing that point. -/
private def clopenTopology (X : Type u) [TopologicalSpace X] :
    GrothendieckTopology (Clopens X) where
  sieves U := {R | ∀ x ∈ U, ∃ (V : Clopens X) (f : V ⟶ U), R f ∧ x ∈ V}
  top_mem' _ _ hx := ⟨_, 𝟙 _, trivial, hx⟩
  pullback_stable' U V R f hR x hx := by
    obtain ⟨W, g, hg, hxW⟩ := hR x (leOfHom f hx)
    exact ⟨W ⊓ V, homOfLE inf_le_right, R.downward_closed hg (homOfLE inf_le_left), hxW, hx⟩
  transitive' U R hR T hT x hx := by
    obtain ⟨V, f, hf, hxV⟩ := hR x hx
    obtain ⟨W, g, hg, hxW⟩ := hT hf x hxV
    exact ⟨W, g ≫ f, hg, hxW⟩

/-- The point of the site of clopen subsets given by a point of the space: its fibre functor
sends a clopen subset to the proposition that it contains the point. -/
private def clopenPoint {X : Type u} [TopologicalSpace X] (x : X) :
    GrothendieckTopology.Point.{u} (clopenTopology X) where
  fiber.obj U := ULift.{u} (PLift (x ∈ U))
  fiber.map f := ↾fun h ↦ ⟨⟨leOfHom f h.down.down⟩⟩
  isCofiltered := {
    nonempty := ⟨Functor.elementsMk _ ⊤ (ULift.up (PLift.up (Set.mem_univ x)))⟩
    cone_objs := by
      intro a b
      have hU : x ∈ a.obj := (a.val : ULift (PLift (x ∈ a.obj))).down.down
      have hV : x ∈ b.obj := (b.val : ULift (PLift (x ∈ b.obj))).down.down
      exact ⟨Functor.elementsMk _ (a.obj ⊓ b.obj) (ULift.up (PLift.up ⟨hU, hV⟩)),
        ⟨homOfLE inf_le_left, rfl⟩, ⟨homOfLE inf_le_right, rfl⟩, trivial⟩
    cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩
  }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    intro U R hR h
    obtain ⟨V, f, hf, hxV⟩ := hR x (h : ULift (PLift (x ∈ U))).down.down
    exact ⟨V, f, hf, ULift.up (PLift.up hxV), rfl⟩

/-- The points of a space form a conservative family of points of its site of clopen
subsets. -/
private theorem clopenTopology_hasEnoughPoints (X : Type u) [TopologicalSpace X] :
    GrothendieckTopology.HasEnoughPoints.{u} (clopenTopology X) := by
  let P := ObjectProperty.ofObj (clopenPoint (X := X))
  refine ⟨P, inferInstance, ?_⟩
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR x hx
  obtain ⟨V, f, hf, y, _⟩ := hR ⟨clopenPoint x, ⟨x⟩⟩
    (ULift.up (PLift.up hx) : ULift (PLift (x ∈ U)))
  exact ⟨V, f, hf, (y : ULift (PLift (x ∈ V))).down.down⟩

/-- A site whose objects with a given property are cover dense has enough points as soon as
each such object is, up to isomorphism, the image of an object of a site with enough points
under a morphism of sites in both directions. -/
private theorem hasConservativeFamily_of_coverDense_sites
    {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
    (J : GrothendieckTopology C) (P : ObjectProperty C) [P.ι.IsCoverDense J]
    (D : P.FullSubcategory → Type w) [∀ p, Category.{w} (D p)]
    (K : ∀ p, GrothendieckTopology (D p)) (G : ∀ p, D p ⥤ C)
    [∀ p, (G p).IsContinuous (K p) J] [∀ p, (G p).IsCocontinuous (K p) J]
    (d : ∀ p, D p) (e : ∀ p, (G p).obj (d p) ≅ p.obj)
    (hK : ∀ p, GrothendieckTopology.HasConservativeFamily.{w} (K p)) :
    GrothendieckTopology.HasConservativeFamily.{w} J := by
  choose Q hQ using fun p ↦
    (GrothendieckTopology.hasConservativeFamily_iff_exists (K p)).1 (hK p)
  refine GrothendieckTopology.IsConservativeFamily.hasConservativeFamily
    (p := fun q : Σ p, ObjectProperty.FullSubcategory (Q p) ↦ q.2.obj.map (G q.1) J) ?_
  intro F G' f hf
  apply Functor.IsCoverDense.iso_of_restrict_iso (G := P.ι) f
  suffices ∀ p, IsIso ((P.ι.op.whiskerLeft f.hom).app p) by
    exact NatIso.isIso_of_isIso_app _
  intro p
  let p := p.unop
  have hfg : IsIso (((G p).sheafPushforwardContinuous (Type w) (K p) J).map f) := by
    apply ((hQ p).jointlyReflectIsomorphisms_type.isIso_iff _).mpr
    intro q
    have h := hf ⟨p, q⟩
    rwa [NatIso.isIso_map_iff (q.obj.sheafFiberMapIso (G p) J (Type w))] at h
  have happ : IsIso (f.hom.app (Opposite.op ((G p).obj (d p)))) :=
    inferInstanceAs (IsIso ((((G p).sheafPushforwardContinuous (Type w) (K p) J).map f).hom.app
      (Opposite.op (d p))))
  exact (NatTrans.isIso_app_iff_of_iso f.hom (e p).op).mpr happ

/-- A clopen subset of a scheme, viewed as an open subset. -/
private abbrev clopenOpen {X : Scheme.{u}} (U : Clopens X) : X.Opens := U.toOpens

/-- The open immersion of one clopen subscheme into a larger one. -/
private noncomputable abbrev clopenHom {X : Scheme.{u}} {U V : Clopens X} (h : U ≤ V) :
    (clopenOpen U).toScheme ⟶ (clopenOpen V).toScheme :=
  X.homOfLE (show clopenOpen U ≤ clopenOpen V from h)

/-- A clopen subscheme of an affine scheme is affine, being a closed subscheme of it. -/
private lemma isAffine_clopen (X : Scheme.{u}) [IsAffine X] (U : Clopens X) :
    IsAffine (clopenOpen U).toScheme := by
  let : IsClosedImmersion (clopenOpen U).ι :=
    IsClosedImmersion.of_isPreimmersion (clopenOpen U).ι (by simpa using U.isClosed)
  exact isAffine_of_isAffineHom (clopenOpen U).ι

/-- Morphisms of affine objects of the small pro-étale site are equal if their underlying
morphisms of schemes are. -/
private lemma affineProetale_hom_ext {S : Scheme.{u}} {X Y : AffineProetale S} {f g : X ⟶ Y}
    (h : f.hom.left = g.hom.left) : f = g := by
  apply ObjectProperty.hom_ext
  apply (Scheme.ProEt.forget S).map_injective
  ext1
  exact h

/-- Restriction of an affine object of the small pro-étale site to its clopen subsets. -/
private noncomputable def clopenRestriction {S : Scheme.{u}} (T : AffineProetale S) :
    Clopens T.obj.left ⥤ AffineProetale S where
  obj U := by
    have : IsAffine T.obj.left := T.property
    exact ⟨Scheme.ProEt.mk ((clopenOpen U).ι ≫ T.obj.hom), isAffine_clopen T.obj.left U⟩
  map {U V} f := ObjectProperty.homMk
    (MorphismProperty.Over.homMk (clopenHom (leOfHom f)) (Scheme.homOfLE_ι_assoc _ _ _))
  map_id U := by
    apply affineProetale_hom_ext
    exact Scheme.homOfLE_rfl _ _
  map_comp f g := by
    apply affineProetale_hom_ext
    change clopenHom (leOfHom (f ≫ g)) = clopenHom (leOfHom f) ≫ clopenHom (leOfHom g)
    exact (Scheme.homOfLE_homOfLE _ _ _).symm

/-- A Zariski covering by open immersions generates a pro-étale covering sieve. -/
private lemma sieve₀_mem_proetaleTopology {T : Scheme.{u}} (E : PreZeroHypercover T)
    (hE : E.presieve₀ ∈ Scheme.zariskiPrecoverage T) :
    E.sieve₀ ∈ Scheme.proetaleTopology T := by
  have : MorphismProperty.ContainsIdentities
      (@WeaklyEtale : MorphismProperty Scheme.{u}) := ⟨fun _ => inferInstance⟩
  exact Scheme.proetalePrecoverage.generate_mem_toGrothendieck
    (Scheme.zariskiPrecoverage_le_propQCPrecoverage _ hE)

/-- On a scheme all of whose pro-étale coverings are refined by a decomposition into clopen
pieces, every pro-étale covering sieve of a clopen subscheme contains the inclusion of a
smaller clopen subscheme around any prescribed point. -/
private lemma clopen_refinement (T : Scheme.{u})
    (hT : ProetaleWContractible.EveryProetaleCoverHasZariskiRefinement T)
    (U : Clopens T) (R : Sieve (clopenOpen U).toScheme)
    (hR : R ∈ Scheme.proetaleTopology _) (x : T) (hx : x ∈ U) :
    ∃ (V : Clopens T) (hVU : V ≤ U), x ∈ V ∧ R (clopenHom hVU) := by
  classical
  let U' : Bool → T.Opens := fun b => if b then (clopenOpen U) else (clopenOpen Uᶜ)
  let E : PreZeroHypercover T := ⟨Bool, fun b => (U' b).toScheme, fun b => (U' b).ι⟩
  have hE : E.presieve₀ ∈ Scheme.zariskiPrecoverage T := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun b => inferInstanceAs (IsOpenImmersion (U' b).ι)⟩
    intro t
    by_cases ht : t ∈ U
    · exact ⟨true, ⟨t, ht⟩, rfl⟩
    · exact ⟨false, ⟨t, ht⟩, rfl⟩
  let Q := R.pushforward (clopenOpen U).ι ⊔
    (⊤ : Sieve (clopenOpen Uᶜ).toScheme).pushforward (clopenOpen Uᶜ).ι
  have hQ : Q ∈ Scheme.proetaleTopology T := by
    apply Scheme.proetaleTopology.transitive (sieve₀_mem_proetaleTopology E hE)
    rintro Z _ ⟨Y, f, g, ⟨b⟩, rfl⟩
    rw [Sieve.pullback_comp]
    apply Scheme.proetaleTopology.pullback_stable
    cases b
    · exact Scheme.proetaleTopology.superset_covering (S := ⊤)
        (fun W k _ => Or.inr ⟨k, rfl, trivial⟩) (Scheme.proetaleTopology.top_mem _)
    · exact Scheme.proetaleTopology.superset_covering (S := R)
        (fun W k hk => Or.inl ⟨k, rfl, hk⟩) hR
  obtain ⟨n, D, f, hd, hf⟩ := hT Q hQ
  have hx' : x ∈ ⋃ i, Set.range (f i).base := by rw [hd.cover]; trivial
  obtain ⟨i, t, ht⟩ := Set.mem_iUnion.mp hx'
  have : IsOpenImmersion (f i) := hd.openImmersion i
  rcases hf i with ⟨a, he, ha⟩ | ⟨a, he, _⟩
  · let V : Clopens T := ⟨Set.range (f i).base, hd.clopen i⟩
    have hVU : V ≤ U := by
      rintro z ⟨z', rfl⟩
      rw [← he]
      exact (a z').2
    refine ⟨V, hVU, ⟨t, ht⟩, ?_⟩
    let e := IsOpenImmersion.isoOfRangeEq (clopenOpen V).ι (f i) (by simp [V])
    have hcomp : e.hom ≫ a = clopenHom hVU := by
      apply (cancel_mono (clopenOpen U).ι).mp
      rw [Category.assoc, he]
      simp [e, clopenHom]
    rw [← hcomp]
    exact R.downward_closed ha e.hom
  · have hn : x ∈ Uᶜ := by
      rw [← ht, ← he]
      exact (a t).2
    exact (hn hx).elim

/-- The underlying scheme of an affine object of the small pro-étale site. -/
private abbrev affineToScheme (S : Scheme.{u}) :=
  AffineProetale.inclusion S ⋙ Scheme.ProEt.forget S ⋙ Over.forget S

/-- A morphism of affine objects of the small pro-étale site from a morphism of the underlying
schemes over the base. -/
private def affineHom {S : Scheme.{u}} {X Y : AffineProetale S}
    (f : X.obj.left ⟶ Y.obj.left) (h : f ≫ Y.obj.hom = X.obj.hom) : X ⟶ Y :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk f h)

private lemma affineToScheme_coverPreserving (S : Scheme.{u}) :
    CoverPreserving (AffineProetale.topology S)
      Scheme.proetaleTopology (affineToScheme S) := by
  have := affineInclusion_isDenseSubsite S
  have h : CoverPreserving (Scheme.ProEt.topology S)
      (Scheme.proetaleTopology.over S) (Scheme.ProEt.forget S) :=
    Functor.isContinuous_iff_coverPreserving.mp inferInstance
  exact (Functor.IsDenseSubsite.coverPreserving _ _ _).comp _ _
    (h.comp _ _ (Scheme.proetaleTopology.over_forget_coverPreserving S))

private lemma affineToScheme_mem_pushforward {S : Scheme.{u}}
    {X Y : AffineProetale S} (R : Sieve X) (f : Y ⟶ X) :
    R.functorPushforward (affineToScheme S) ((affineToScheme S).map f) ↔ R f := by
  constructor
  · rintro ⟨Z, g, a, hg, he⟩
    have hw : (affineToScheme S).map g ≫ X.obj.hom = Z.obj.hom :=
      Over.w ((Scheme.ProEt.forget S).map g.hom)
    have hw' : (affineToScheme S).map f ≫ X.obj.hom = Y.obj.hom :=
      Over.w ((Scheme.ProEt.forget S).map f.hom)
    have ha : a ≫ Z.obj.hom = Y.obj.hom :=
      (congrArg (fun k => a ≫ k) hw).symm.trans
        ((Category.assoc a ((affineToScheme S).map g) X.obj.hom).symm.trans
          ((congrArg (fun k => k ≫ X.obj.hom) he.symm).trans hw'))
    have he' : affineHom a ha ≫ g = f := affineProetale_hom_ext he.symm
    rw [← he']
    exact R.downward_closed hg (affineHom a ha)
  · exact fun hf => ⟨Y, f, 𝟙 _, hf, by simp⟩

private lemma clopenRestriction_cocontinuous {S : Scheme.{u}} (T : AffineProetale S)
    (hT : ProetaleWContractible.EveryProetaleCoverHasZariskiRefinement T.obj.left) :
    (clopenRestriction T).IsCocontinuous (clopenTopology T.obj.left)
      (AffineProetale.topology S) := by
  constructor
  intro U R hR x hx
  obtain ⟨V, hVU, hxV, hV⟩ := clopen_refinement T.obj.left hT U
    (R.functorPushforward (affineToScheme S))
    ((affineToScheme_coverPreserving S).cover_preserve hR) x hx
  exact ⟨V, homOfLE hVU,
    (affineToScheme_mem_pushforward R ((clopenRestriction T).map (homOfLE hVU))).mp hV,
    hxV⟩

private lemma affine_mem_topology_iff {S : Scheme.{u}} {X : AffineProetale S} (R : Sieve X) :
    R ∈ AffineProetale.topology S X ↔
      R.functorPushforward (affineToScheme S) ∈ Scheme.proetaleTopology _ := by
  have := affineInclusion_isDenseSubsite S
  rw [← Functor.functorPushforward_mem_iff
    (J := AffineProetale.topology S) (K := Scheme.ProEt.topology S)
    (G := AffineProetale.inclusion S)]
  let F := Scheme.ProEt.forget S
  let K := Scheme.proetaleTopology.over S
  have : F.IsContinuous (F.restrictedTopology K) K :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      (F.coverPreserving_restrictedTopology K)
  rw [Scheme.ProEt.topology_eq_inducedTopology,
    ← Functor.restrictedTopology_eq_inducedTopology, Functor.mem_restrictedTopology_iff]
  show ((R.functorPushforward (AffineProetale.inclusion S)).functorPushforward
      (Scheme.ProEt.forget S)).functorPushforward (Over.forget S) ∈ Scheme.proetaleTopology _ ↔ _
  simp only [← Sieve.functorPushforward_comp, affineToScheme]
  rfl

/-- Affine objects of the small pro-étale site all of whose pro-étale coverings are refined by
a decomposition into clopen pieces. -/
private abbrev clopenRefinementProperty (S : Scheme.{u}) : ObjectProperty (AffineProetale S) :=
  fun T => ProetaleWContractible.EveryProetaleCoverHasZariskiRefinement T.obj.left

private lemma clopenRestriction_coverPreserving {S : Scheme.{u}} (T : AffineProetale S) :
    CoverPreserving (clopenTopology T.obj.left) (AffineProetale.topology S)
      (clopenRestriction T) := by
  classical
  constructor
  intro U R hR
  choose V f hf hx using fun x : U => hR x.val x.property
  let E : PreZeroHypercover (clopenOpen U).toScheme :=
    ⟨U, fun x => (clopenOpen (V x)).toScheme, fun x => clopenHom (leOfHom (f x))⟩
  have hE : E.presieve₀ ∈ Scheme.zariskiPrecoverage _ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ⟨x, ⟨x.val, hx x⟩, ?_⟩, fun x => inferInstance⟩
    exact Subtype.ext (Scheme.homOfLE_apply (leOfHom (f x)) _)
  apply (affine_mem_topology_iff _).mpr
  apply Scheme.proetaleTopology.superset_covering (S := E.sieve₀) _
    (sieve₀_mem_proetaleTopology E hE)
  apply (Sieve.generate_le_iff _ _).2
  rintro Y g ⟨x⟩
  exact (affineToScheme_mem_pushforward _ ((clopenRestriction T).map (f x))).mpr
    ⟨V x, f x, 𝟙 _, hf x, by simp⟩

private lemma clopenRestriction_compatiblePreserving {S : Scheme.{u}} (T : AffineProetale S) :
    CompatiblePreserving (AffineProetale.topology S) (clopenRestriction T) := by
  let F := clopenRestriction T
  let H := affineToScheme S
  let : CreatesLimitsOfShape Limits.WalkingCospan (AffineProetale.inclusion S) :=
    affineCreatesPullbacks (Scheme.ProEt.forget S ⋙ Over.forget S)
  constructor
  intro ℱ Z R x hx U V Y f₁ f₂ g₁ g₂ hg₁ hg₂ he
  let a : U ⊓ V ⟶ U := homOfLE inf_le_left
  let b : U ⊓ V ⟶ V := homOfLE inf_le_right
  have hp : IsPullback (F.map a) (F.map b) (F.map g₁) (F.map g₂) :=
    IsPullback.of_map_of_faithful H
      (isPullback_opens_inf_le (show clopenOpen U ≤ clopenOpen Z from leOfHom g₁)
        (show clopenOpen V ≤ clopenOpen Z from leOfHom g₂))
  let l := hp.lift f₁ f₂ he
  have hh := hx a b hg₁ hg₂ (Subsingleton.elim _ _)
  have e₁ : l ≫ F.map a = f₁ := hp.lift_fst _ _ _
  have e₂ : l ≫ F.map b = f₂ := hp.lift_snd _ _ _
  rw [← e₁, ← e₂, op_comp, op_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  exact congrArg (ℱ.obj.map l.op) hh

private lemma clopenRestriction_continuous {S : Scheme.{u}} (T : AffineProetale S) :
    (clopenRestriction T).IsContinuous (clopenTopology T.obj.left)
      (AffineProetale.topology S) :=
  Functor.isContinuous_of_coverPreserving (clopenRestriction_compatiblePreserving T)
    (clopenRestriction_coverPreserving T)

private theorem conservative_of_coverDense_clopenRefinements (S : Scheme.{u})
    [(clopenRefinementProperty S).ι.IsCoverDense (AffineProetale.topology S)] :
    GrothendieckTopology.HasConservativeFamily.{u} (AffineProetale.topology S) := by
  let P := clopenRefinementProperty S
  let J := AffineProetale.topology S
  have (T : P.FullSubcategory) : (clopenRestriction T.obj).IsCocontinuous
      (clopenTopology T.obj.obj.left) J := clopenRestriction_cocontinuous T.obj T.property
  have (T : P.FullSubcategory) : (clopenRestriction T.obj).IsContinuous
      (clopenTopology T.obj.obj.left) J := clopenRestriction_continuous T.obj
  apply hasConservativeFamily_of_coverDense_sites J P
    (fun T => Clopens T.obj.obj.left) (fun T => clopenTopology T.obj.obj.left)
    (fun T => clopenRestriction T.obj) (fun _ => ⊤)
    (fun T => ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk T.obj.obj.left.topIso rfl))
  intro T
  have := clopenTopology_hasEnoughPoints T.obj.obj.left
  exact GrothendieckTopology.HasConservativeFamily.of_hasEnoughPoints _

/-- Every affine object of the small pro-étale site is covered by the spectrum of a
w-contractible ring, over which every pro-étale covering has a clopen refinement. -/
private lemma clopenRefinement_coverDense (S : Scheme.{u}) :
    (clopenRefinementProperty S).ι.IsCoverDense (AffineProetale.topology S) := by
  constructor
  intro X
  have : IsAffine X.obj.left := X.property
  let A := Γ(X.obj.left, ⊤)
  obtain ⟨D, hD, f, hff, hind, hw⟩ := exists_faithfullyFlat_ind_etale_wContractible A
  let : CommRing D := hD
  let : Algebra A D := f.toAlgebra
  have hind' : (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A D) := by
    change ObjectProperty.ind.{u} (MorphismProperty.underObj CommRingCat.etale)
      (Under.mk (CommRingCat.ofHom f)) at hind
    rw [← MorphismProperty.ind_iff_ind_underMk] at hind
    exact CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hind
  have hweak : Algebra.WeaklyEtale A D :=
    Algebra.weaklyEtale_of_ind_etale (StacksDraft.indEtale_iff.mpr hind')
  let δ := Spec.map (CommRingCat.ofHom f)
  have : WeaklyEtale δ := (weaklyEtale_specMap_iff _).mpr hweak
  have : Surjective δ := ⟨(RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff).2⟩
  let φ := δ ≫ X.obj.left.isoSpec.inv
  let Y : AffineProetale S :=
    ⟨Scheme.ProEt.mk (φ ≫ X.obj.hom), inferInstanceAs (IsAffine (Spec (.of D)))⟩
  let g : Y ⟶ X := affineHom φ rfl
  have hY : clopenRefinementProperty S Y :=
    ProetaleWContractible.everyProetaleCoverHasZariskiRefinement_of_wContractible D hw
  have hcov : (Sieve.coverByImage (clopenRefinementProperty S).ι X).arrows g :=
    Presieve.in_coverByImage (clopenRefinementProperty S).ι (Y := ⟨Y, hY⟩) g
  apply (affine_mem_topology_iff _).mpr
  apply Scheme.proetaleTopology.superset_covering (S := Sieve.generate (Presieve.singleton φ)) _
    (Scheme.Hom.generate_singleton_mem_propQCTopology φ (inferInstance : WeaklyEtale φ))
  apply (Sieve.generate_le_iff _ _).2
  rintro Z p ⟨⟩
  exact (affineToScheme_mem_pushforward _ g).mpr hcov

/-- The affine objects of the small pro-étale site of a scheme have enough points. -/
public theorem smallAffineProetale_hasConservativeFamily (S : Scheme.{u}) :
    GrothendieckTopology.HasConservativeFamily.{u} (AffineProetale.topology S) := by
  have := clopenRefinement_coverDense S
  exact conservative_of_coverDense_clopenRefinements S

/-- Every covering of the big affine pro-étale site is finite, so Deligne's criterion gives a
small conservative family of points. -/
@[sga "2 XIV 1.9" "special case"]
private theorem bigAffineProetale_hasEnoughPoints
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (BigAffineProetale.topology B S hS) := by
  let C := BigAffineProetale B S hS
  let K := BigAffineProetale.precoverage B S hS
  let J := BigAffineProetale.topology B S hS
  have : Limits.HasPullbacks C := inferInstance
  have : Small.{u + 1} C := inferInstance
  have : LocallySmall.{u + 1} C := inferInstance
  apply GrothendieckTopology.hasEnoughPoints_of_exists_finite_refinement J
  intro X R hR
  obtain ⟨E, hFinite, hLe, hCover⟩ :=
    CategoryTheory.finite_refinement_saturate K (by
      intro X R hR
      obtain ⟨E, hEq, hCov⟩ := (BigAffineProetale.mem_precoverage_iff B S hS).mp hR
      exact ⟨E, hCov.2, hEq⟩) ((K.mem_toGrothendieck_iff).mp hR)
  let : Fintype E.I₀ := Fintype.ofFinite E.I₀
  let e : Fin (Fintype.card E.I₀) ≃ E.I₀ := (Fintype.equivFin E.I₀).symm
  let F := E.reindex e
  have hReindex : F.sieve₀ = E.sieve₀ := congrArg Sieve.generate (E.presieve₀_reindex e)
  refine ⟨F.I₀, ?_, F.X, F.f, ?_, ?_⟩
  · show Finite (Fin (Fintype.card E.I₀)); infer_instance
  · simpa [hReindex] using hLe
  · simpa [hReindex] using hCover

/-- The affine objects of the big pro-étale site over a scheme have enough points. -/
public theorem bigAffineProetale_hasConservativeFamily
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    GrothendieckTopology.HasConservativeFamily.{u + 1}
      (BigAffineProetale.topology B S hS) :=
  have := bigAffineProetale_hasEnoughPoints B S hS
  GrothendieckTopology.HasConservativeFamily.of_hasEnoughPoints
    (BigAffineProetale.topology B S hS)

/-- The big pro-étale site over a scheme has enough points. -/
public theorem bigProetaleOver_hasConservativeFamily
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    GrothendieckTopology.HasConservativeFamily.{u + 1}
      (BigProetaleOver.topology B S hS) := by
  let G := BigAffineProetale.inclusion B S hS
  let J := BigAffineProetale.topology B S hS
  let K := BigProetaleOver.topology B S hS
  have : LocallySmall.{u + 1} (BigProetaleOver B S hS) := inferInstance
  let : G.IsDenseSubsite J K := (inclusion_isSpecialCocontinuous B S hS).2
  exact CategoryTheory.hasConservativeFamily_of_denseSubsite J K G
    (bigAffineProetale_hasConservativeFamily B S hS)

/-- A chosen pro-étale site of schemes has enough points. -/
public theorem schemeProetale_hasConservativeFamily (B : BigProetaleSite.{u}) :
    GrothendieckTopology.HasConservativeFamily.{u + 1} B.topology := by
  let T := specZObject B
  have hT : Limits.IsTerminal T := specZObject_isTerminal B
  let e := Over.equivalenceOfIsTerminal hT
  let : (Over.forget T).IsEquivalence := e.isEquivalence_functor
  let : (Over.forget T).IsDenseSubsite (B.topology.over T) B.topology :=
    { functorPushforward_mem_iff := Iff.rfl }
  have : LocallySmall.{u + 1} B.Scheme := inferInstance
  apply CategoryTheory.hasConservativeFamily_of_denseSubsite (B.topology.over T) B.topology
    (Over.forget T)
  exact bigProetaleOver_hasConservativeFamily B T.obj T.property

/-- The small pro-étale site of a scheme has enough points. -/
public theorem smallProetale_hasConservativeFamily (S : Scheme.{u}) :
    GrothendieckTopology.HasConservativeFamily.{u} (Scheme.ProEt.topology S) := by
  let G := AffineProetale.inclusion S
  let J := AffineProetale.topology S
  let K := Scheme.ProEt.topology S
  have : LocallySmall.{u} (AffineProetale S) := inferInstance
  have : LocallySmall.{u} (Scheme.ProEt S) := inferInstance
  let : G.IsDenseSubsite J K := affineInclusion_isDenseSubsite S
  exact CategoryTheory.hasConservativeFamily_of_denseSubsite J K G
    (smallAffineProetale_hasConservativeFamily S)

/-- **Stacks 0992.** The pro-étale sites of schemes, the small pro-étale site of a scheme, the
big pro-étale site over it, the affine objects of the small site and the affine objects of the
big site all have enough points. -/
@[stacks 0992]
public theorem proetale_hasEnoughPoints
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    GrothendieckTopology.HasConservativeFamily.{u + 1} B.topology ∧
      GrothendieckTopology.HasConservativeFamily.{u} (Scheme.ProEt.topology S) ∧
      GrothendieckTopology.HasConservativeFamily.{u + 1} (BigProetaleOver.topology B S hS) ∧
      GrothendieckTopology.HasConservativeFamily.{u} (AffineProetale.topology S) ∧
      GrothendieckTopology.HasConservativeFamily.{u + 1}
        (BigAffineProetale.topology B S hS) :=
  ⟨schemeProetale_hasConservativeFamily B, smallProetale_hasConservativeFamily S,
    bigProetaleOver_hasConservativeFamily B S hS,
    smallAffineProetale_hasConservativeFamily S,
    bigAffineProetale_hasConservativeFamily B S hS⟩

end AlgebraicGeometry.ProEtale

end
