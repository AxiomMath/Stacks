module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Morphisms
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.PointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationSurgery
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf

/-!
# Loci defined by a condition on the geometric stalks

Let `X` be a quasi-compact quasi-separated scheme. For a map of constructible sheaves of sets on
`X_étale`, the set of points where the induced map of geometric stalks is surjective, injective,
or isomorphic to a given map of sets is constructible in `X`; and the support of a constructible
abelian sheaf, or of a constructible sheaf of modules over a Noetherian ring, is constructible.
This is Tag 09YS.

The argument is the one of the source. Both sheaves become finite locally constant on the strata
of one constructible stratification of `X`, by Tag 095E and a common refinement. On a stratum the
map is, on an étale covering, the map of constant sheaves attached to a map of sets, by Tag 093S,
so the geometric stalk at any point of a member of the covering is that map of sets; as the stalk
condition does not depend on the chosen geometric point above a point of the scheme, the locus and
its complement are both unions of the open images of members of the covering, and the locus is
therefore open and closed in the stratum. A relatively clopen subset of a stratum is a
quasi-compact open of a spectral space, hence constructible there, and the immersion of a stratum
carries it to a constructible subset of `X` by Tag 09YJ.

## Main results

* `AlgebraicGeometry.isConstructible_of_isClopen_preimage_strata` — a subset whose preimage in
  every stratum of a constructible stratification of the whole scheme is clopen is constructible.
* `AlgebraicGeometry.isClopen_setOf_exists_geometricPoint_property_etaleStalk_map` and
  `AlgebraicGeometry.isClopen_setOf_exists_geometricPoint_property_etaleStalk` — the stratum-level
  statements, for a morphism and for a single sheaf.
* `AlgebraicGeometry.isConstructible_setOf_exists_geometricPoint_property_etaleStalk_map` and
  `AlgebraicGeometry.isConstructible_setOf_exists_geometricPoint_property_etaleStalk` — the two
  global statements, for an arbitrary isomorphism-invariant property.
* `AlgebraicGeometry.isConstructible_setOf_surjective_etaleStalk_map`,
  `AlgebraicGeometry.isConstructible_setOf_injective_etaleStalk_map` and
  `AlgebraicGeometry.isConstructible_setOf_etaleStalk_map_iso` — **Tag 09YS, part (1)**.
* `AlgebraicGeometry.isConstructible_supportSheaf` — **Tag 09YS, part (2)**.
* `AlgebraicGeometry.isConstructible_support_moduleSheaf` — **Tag 09YS, part (3)**.

## Implementation notes

The locus is described, as the support of an abelian sheaf is in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SupportSheaf.lean`, by *some* geometric point above
the given point satisfying the condition. This is the same set as the one described by *every*
geometric point above it, because the stalk functors at two geometric points with the same image
are isomorphic; that isomorphism is
`AlgebraicGeometry.etaleStalkPresheafFunctorIsoOfEqBase` and it is used in both proofs.

Part (3) carries the size hypotheses `UnivLE.{u, w}` and
`PreservesFilteredColimitsOfSize.{max u w, max u w} (forget (ModuleCat.{max u w} Λ))`, which say
that the coefficient universe is large enough for the geometric stalk of a sheaf of modules to
exist and to be computed by the underlying filtered colimit; part (2) carries only the first.
Neither restricts the mathematics of the source, which does not track universes.

## References

* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
* [Stacks Project, Tag 09YJ](https://stacks.math.columbia.edu/tag/09YJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe v w u

namespace AlgebraicGeometry

/-- A subset of a quasi-compact quasi-separated scheme whose preimage in every stratum of a
constructible stratification of the whole scheme is open and closed is constructible. -/
public theorem isConstructible_of_isClopen_preimage_strata (B : BigEtaleSite.{u})
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (s : ConstructibleStratification B X ⊤) (L : Set X.obj)
    (h : ∀ k, IsClopen ((B.inclusion.map (s.inclusion k)).base ⁻¹' L)) :
    IsConstructible L := by
  have hcX : CompactSpace ↥(B.inclusion.obj X) := inferInstanceAs (CompactSpace ↥X.obj)
  have hqX : QuasiSeparatedSpace ↥(B.inclusion.obj X) :=
    inferInstanceAs (QuasiSeparatedSpace ↥X.obj)
  have hX : SpectralSpace ↥(B.inclusion.obj X) := ⟨⟩
  have key : ∀ k, IsConstructible (⇑(B.inclusion.map (s.inclusion k)).base ''
      ((B.inclusion.map (s.inclusion k)).base ⁻¹' L)) := by
    intro k
    have := s.isImmersion k
    have hr := (isConstructible_top_ι_preimage_iff (Y := B.inclusion.obj X)
      (Set.range ⇑(B.inclusion.map (s.inclusion k)).base)).mp (s.constructible k)
    have hsp := spectralSpace_of_isImmersion_of_isConstructible_range
      (B.inclusion.map (s.inclusion k)) hr
    exact (B.inclusion.map (s.inclusion k)).isEmbedding
      |>.isConstructible_image_of_isConstructible_range hr
        (((h k).isClosed.isCompact).isConstructible (h k).isOpen)
  have hcov : L = ⋃ k, ⇑(B.inclusion.map (s.inclusion k)).base ''
      ((B.inclusion.map (s.inclusion k)).base ⁻¹' L) := by
    have huniv : (Set.univ : Set X.obj) =
        ⋃ k, Set.range ⇑(B.inclusion.map (s.inclusion k)).base := by
      simpa using s.covers
    simp only [Set.image_preimage_eq_inter_range, ← Set.inter_iUnion, ← huniv, Set.inter_univ]
  rw [hcov]
  exact IsConstructible.iUnion key

/-- The image of a geometric point under a morphism of schemes lies over the image of the point
it lies over. -/
private theorem GeometricPoint.LiesOver.map {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    {x : GeometricPoint Z} {z : Z} (hx : x.LiesOver z) : (x.map f).LiesOver (f.base z) := by
  simp only [GeometricPoint.LiesOver, GeometricPoint.map_hom] at hx ⊢
  simpa using congrArg f.base hx

/-- For a condition on geometric points depending only on the image point, the set of points over
which some geometric point satisfies the condition is closed as soon as the set of points over
which some geometric point violates it is open. -/
private theorem isClosed_setOf_exists_geometricPoint_liesOver {S : Scheme.{u}}
    (Q : GeometricPoint S → Prop)
    (hQ : ∀ {p q : GeometricPoint S}, p.hom default = q.hom default → (Q p ↔ Q q))
    (h : IsOpen {z : S | ∃ t : GeometricPoint S, t.LiesOver z ∧ ¬ Q t}) :
    IsClosed {z : S | ∃ t : GeometricPoint S, t.LiesOver z ∧ Q t} := by
  rw [← isOpen_compl_iff]
  convert h using 1
  ext z
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and]
  refine ⟨fun hz => ⟨GeometricPoint.ofPoint S z, GeometricPoint.ofPoint_liesOver S z,
    hz _ (GeometricPoint.ofPoint_liesOver S z)⟩, ?_⟩
  rintro ⟨t, htz, hnt⟩ t' ht'z hQt'
  exact hnt ((hQ (ht'z.trans htz.symm)).mp hQt')

/-- A condition on geometric points depending only on the image point defines a clopen set of
points if both it and its negation are described by an open cover. -/
private theorem isClopen_setOf_exists_geometricPoint_of_cover {S : Scheme.{u}} {ι : Type*}
    (U : ι → Set S) (hU : ∀ i, IsOpen (U i)) (Q : GeometricPoint S → Prop)
    (hQ : ∀ {p q : GeometricPoint S}, p.hom default = q.hom default → (Q p ↔ Q q))
    (p : ι → Prop) (h : ∀ z : S, (∃ t : GeometricPoint S, t.LiesOver z ∧ Q t) ↔ ∃ i, p i ∧ z ∈ U i)
    (h' : ∀ z : S, (∃ t : GeometricPoint S, t.LiesOver z ∧ ¬ Q t) ↔ ∃ i, ¬ p i ∧ z ∈ U i) :
    IsClopen {z : S | ∃ t : GeometricPoint S, t.LiesOver z ∧ Q t} := by
  have hopen : ∀ {p : ι → Prop} {T : Set S}, (∀ z, z ∈ T ↔ ∃ i, p i ∧ z ∈ U i) → IsOpen T :=
    fun {p T} h => by
      rw [show T = ⋃ i ∈ {i | p i}, U i from Set.ext fun z => by rw [h z]; simp]
      exact isOpen_biUnion fun i _ => hU i
  exact ⟨isClosed_setOf_exists_geometricPoint_liesOver Q hQ (hopen h'), hopen h⟩

/-- The preimage under a morphism of schemes of the locus of a condition on geometric points of the
target is the locus of the pulled back condition. -/
private theorem preimage_setOf_exists_geometricPoint_liesOver {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    (Q : GeometricPoint Y → Prop) (Q' : GeometricPoint Z → Prop)
    (hQ : ∀ {p q : GeometricPoint Y}, p.hom default = q.hom default → (Q p ↔ Q q))
    (hpull : ∀ x : GeometricPoint Z, Q' x ↔ Q (x.map f)) :
    f.base ⁻¹' {y : Y | ∃ t : GeometricPoint Y, t.LiesOver y ∧ Q t} =
      {z : Z | ∃ x : GeometricPoint Z, x.LiesOver z ∧ Q' x} := by
  ext z
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨t, htz, hQt⟩
    refine ⟨GeometricPoint.ofPoint _ z, GeometricPoint.ofPoint_liesOver _ z, (hpull _).mpr ?_⟩
    refine (hQ (p := t) (q := (GeometricPoint.ofPoint _ z).map f) ?_).mp hQt
    rw [htz]
    exact ((GeometricPoint.ofPoint_liesOver _ z).map f).symm
  · rintro ⟨x, hxz, hQx⟩
    exact ⟨x.map f, hxz.map f, (hpull x).mp hQx⟩

section Sets

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- NO `geometricPointFiberFinal` HERE. It had a byte-identical type to the public
-- `AlgebraicGeometry.SmallEtale.finalLift`
-- (`StacksFrontier/AlgebraicGeometry/Etale/SupportSheaf.lean`:84) and the same term `⟨t.hom, _⟩`,
-- whose second component is a proof and so proof-irrelevant: the two were definitionally one
-- declaration under two names. The use below names the survivor.

/-- A lift of a geometric point to an object of the small étale site sits above the image of the
geometric point. -/
public theorem geometricPointFiber_structure_base (t : GeometricPoint S)
    {U : SmallEtale B S hS} (y : (geometricPointFiber B S hS t).obj U) :
    (B.inclusion.map U.obj.hom).base (y.1.base default) = t.hom.base default := by
  simpa using congrArg (fun m : t.source ⟶ S => m.base default) y.2

/-- Every geometric point of `S` lifts to a member of any covering family of the final object of
the small étale site of `S`; the lift sits above the image of the geometric point. -/
public theorem exists_geometricPointFiber_of_coverFinal {I : Type*}
    (V : I → SmallEtale B S hS) (f : ∀ i, V i ⟶ SmallEtale.final B S hS)
    (hf : Sieve.ofArrows V f ∈ SmallEtale.topology B S hS (SmallEtale.final B S hS))
    (t : GeometricPoint S) :
    ∃ (i : I) (y : (geometricPointFiber B S hS t).obj (V i)),
      (B.inclusion.map (V i).obj.hom).base (y.1.base default) = t.hom.base default := by
  obtain ⟨Y, g, hg, y', hy'⟩ := geometricPointFiber_jointly_surjective B S hS t
    (Sieve.ofArrows V f) hf (SmallEtale.finalLift B S hS t)
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).mp hg
  exact ⟨i, (geometricPointFiber B S hS t).map a y',
    geometricPointFiber_structure_base B S hS t _⟩

/-- A point of an object of the small étale site of `S` is the image of a geometric point of `S`
which lifts to that object. -/
public theorem exists_geometricPoint_fiber_of_point (U : SmallEtale B S hS)
    (v : (SmallEtale.toScheme B S hS).obj U) :
    ∃ (t : GeometricPoint S) (_ : (geometricPointFiber B S hS t).obj U),
      t.LiesOver ((B.inclusion.map U.obj.hom).base v) := by
  refine ⟨(GeometricPoint.ofPoint ((SmallEtale.toScheme B S hS).obj U) v).map
    (B.inclusion.map U.obj.hom), ⟨(GeometricPoint.ofPoint _ v).hom, rfl⟩, ?_⟩
  have h := GeometricPoint.ofPoint_liesOver ((SmallEtale.toScheme B S hS).obj U) v
  simp only [GeometricPoint.LiesOver, GeometricPoint.map_hom] at h ⊢
  simp

/-- A property of maps of sets depending only on the isomorphism class of the map takes the same
value on the maps induced on the stalks at two geometric points above one point of `S`. -/
public theorem property_etaleStalk_map_iff_of_base_eq
    {F G : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))} (φ : F ⟶ G)
    (P : ∀ A C : Type (u + 1), (A → C) → Prop)
    (hP : ∀ (A C A' C' : Type (u + 1)) (g : A → C) (g' : A' → C') (a : A ≃ A') (c : C ≃ C'),
      (∀ z, c (g z) = g' (a z)) → (P A C g ↔ P A' C' g'))
    {p q : GeometricPoint S} (h : p.hom default = q.hom default) :
    P _ _ ((etaleStalkPresheafFunctor B S hS p (Type (u + 1))).map φ.hom) ↔
      P _ _ ((etaleStalkPresheafFunctor B S hS q (Type (u + 1))).map φ.hom) :=
  hP _ _ _ _ _ _
    ((etaleStalkPresheafFunctorIsoOfEqBase B S hS h (Type (u + 1))).app F.obj).toEquiv
    ((etaleStalkPresheafFunctorIsoOfEqBase B S hS h (Type (u + 1))).app G.obj).toEquiv
    fun z => by simp

/-- **The locus of a stalkwise condition on a scheme carrying finite locally constant sheaves.**
If `F` is finite locally constant and `G` locally constant on the small étale site of `S`, then
the set of points at which the map induced by `φ` on some geometric stalk has an
isomorphism-invariant property is open and closed: on a covering family trivializing `φ` the
condition is read off the corresponding map of sets, so the locus and its complement are both
unions of the open images of members of the family. -/
public theorem isClopen_setOf_exists_geometricPoint_property_etaleStalk_map
    {F G : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))} (φ : F ⟶ G)
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS) F]
    [Stacks.ConstantSheaf.IsLocallyConstant (SmallEtale.topology B S hS) G]
    (P : ∀ A C : Type (u + 1), (A → C) → Prop)
    (hP : ∀ (A C A' C' : Type (u + 1)) (g : A → C) (g' : A' → C') (a : A ≃ A') (c : C ≃ C'),
      (∀ z, c (g z) = g' (a z)) → (P A C g ↔ P A' C' g')) :
    IsClopen {z : S | ∃ t : GeometricPoint S, t.LiesOver z ∧
      P _ _ ((etaleStalkPresheafFunctor B S hS t (Type (u + 1))).map φ.hom)} := by
  classical
  obtain ⟨I, V, cov, hcov, hdata⟩ :=
    Stacks.ConstantSheaf.exists_cover_restrict_eq_constantSheaf_map
      (SmallEtale.topology B S hS) F G φ (SmallEtale.final B S hS)
  choose A₀ C₀ hfin g eF eG hsq using hdata
  have key : ∀ (Q : ∀ A C : Type (u + 1), (A → C) → Prop),
      (∀ (A C A' C' : Type (u + 1)) (m : A → C) (m' : A' → C') (a : A ≃ A') (c : C ≃ C'),
        (∀ z, c (m z) = m' (a z)) → (Q A C m ↔ Q A' C' m')) → ∀ z : S,
      (∃ t : GeometricPoint S, t.LiesOver z ∧
          Q _ _ ((etaleStalkPresheafFunctor B S hS t (Type (u + 1))).map φ.hom)) ↔
        ∃ i, Q _ _ (g i) ∧ z ∈ Set.range ⇑(B.inclusion.map (V i).obj.hom).base := by
    intro Q hQ z
    constructor
    · rintro ⟨t, htz, hQt⟩
      obtain ⟨i, y, hy⟩ := exists_geometricPointFiber_of_coverFinal B S hS V cov hcov t
      obtain ⟨uF, uG, hu⟩ := Stacks.ConstantSheaf.exists_equiv_sheafFiber_map_of_constantOver
        (geometricPointSitePoint B S hS t) y φ (g i) (eF i) (eG i) (hsq i)
      exact ⟨i, (hQ _ _ _ _ _ _ uF uG hu).mp hQt, y.1.base default, hy.trans htz⟩
    · rintro ⟨i, hQg, v, hv⟩
      obtain ⟨t, y, htz⟩ := exists_geometricPoint_fiber_of_point B S hS (V i) v
      obtain ⟨uF, uG, hu⟩ := Stacks.ConstantSheaf.exists_equiv_sheafFiber_map_of_constantOver
        (geometricPointSitePoint B S hS t) y φ (g i) (eF i) (eG i) (hsq i)
      exact ⟨t, hv ▸ htz, (hQ _ _ _ _ _ _ uF uG hu).mpr hQg⟩
  exact isClopen_setOf_exists_geometricPoint_of_cover
    (fun i => Set.range ⇑(B.inclusion.map (V i).obj.hom).base)
    (fun i => (B.inclusion.map (V i).obj.hom).isOpenMap.isOpen_range)
    (fun t => P _ _ ((etaleStalkPresheafFunctor B S hS t (Type (u + 1))).map φ.hom))
    (property_etaleStalk_map_iff_of_base_eq B S hS φ P hP) (fun i => P _ _ (g i))
    (key P hP) (key (fun A C m => ¬ P A C m) fun A C A' C' m m' a c h =>
      not_congr (hP A C A' C' m m' a c h))

/-- A property of maps of sets invariant under isomorphism of maps takes the same value on the
stalk map of a morphism of sheaves at a geometric point of the source of a morphism of schemes
and on the stalk map of its inverse image. -/
public theorem property_etaleStalk_map_pullback_iff {T : B.Scheme} {Y : B.Scheme} (f : T ⟶ Y)
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    {F G : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type (u + 1))} (φ : F ⟶ G)
    (x : GeometricPoint T.obj)
    (P : ∀ A C : Type (u + 1), (A → C) → Prop)
    (hP : ∀ (A C A' C' : Type (u + 1)) (m : A → C) (m' : A' → C') (a : A ≃ A') (c : C ≃ C'),
      (∀ z, c (m z) = m' (a z)) → (P A C m ↔ P A' C' m')) :
    P _ _ ((etaleStalkPresheafFunctor B T.obj T.property x (Type (u + 1))).map
        (((smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B T.obj T.property)).map φ).hom) ↔
      P _ _ ((etaleStalkPresheafFunctor B Y.obj Y.property
        (x.map (B.inclusion.map f)) (Type (u + 1))).map φ.hom) := by
  have hnat : ∀ z, (smallEtalePullbackSheafFiberIso B f x (Type (u + 1))).hom.app G
        ((geometricPointSitePoint B T.obj T.property x).sheafFiber.map
          (((smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B T.obj T.property)).map φ) z) =
      (geometricPointSitePoint B Y.obj Y.property
          (x.map (B.inclusion.map f))).sheafFiber.map φ
        ((smallEtalePullbackSheafFiberIso B f x (Type (u + 1))).hom.app F z) := by
    intro z
    simpa using ConcreteCategory.congr_hom
      ((smallEtalePullbackSheafFiberIso B f x (Type (u + 1))).hom.naturality φ) z
  exact hP _ _ _ _ _ _
    ((smallEtalePullbackSheafFiberIso B f x (Type (u + 1))).app F).toEquiv
    ((smallEtalePullbackSheafFiberIso B f x (Type (u + 1))).app G).toEquiv hnat

/-- **Tag 09YS, part (1), for an arbitrary isomorphism-invariant property of maps of sets.** On a
quasi-compact quasi-separated scheme, the set of points at which the map induced by a morphism of
constructible sheaves of sets on a geometric stalk has such a property is constructible. -/
public theorem isConstructible_setOf_exists_geometricPoint_property_etaleStalk_map
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (φ : F ⟶ G)
    (hF : IsConstructibleSetSheaf B X F) (hG : IsConstructibleSetSheaf B X G)
    (P : ∀ A C : Type (u + 1), (A → C) → Prop)
    (hP : ∀ (A C A' C' : Type (u + 1)) (m : A → C) (m' : A' → C') (a : A ≃ A') (c : C ≃ C'),
      (∀ z, c (m z) = m' (a z)) → (P A C m ↔ P A' C' m')) :
    IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      P _ _ ((etaleStalkPresheafFunctor B X.obj X.property t (Type (u + 1))).map φ.hom)} := by
  classical
  obtain ⟨sF, hsF⟩ := (isConstructibleFiniteSheaf_iff_exists_stratification B X F).mp hF
  obtain ⟨sG, hsG⟩ := (isConstructibleFiniteSheaf_iff_exists_stratification B X G).mp hG
  set r := sF.inf sG with hr
  have hrF : ∀ k, Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B (r.piece k).obj (r.piece k).property)
      ((smallEtaleSheafPullback B (Type (u + 1)) (r.inclusion k)).obj F) := fun k =>
    ConstructibleStratification.isFiniteLocallyConstant_of_refines _ F hsF
      (fun l => let ⟨i, a, _, hcomm⟩ := ConstructibleStratification.inf_refines_fst sF sG l
        ⟨i, a, hcomm⟩) k
  have hrG : ∀ k, Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B (r.piece k).obj (r.piece k).property)
      ((smallEtaleSheafPullback B (Type (u + 1)) (r.inclusion k)).obj G) := fun k =>
    ConstructibleStratification.isFiniteLocallyConstant_of_refines _ G hsG
      (fun l => let ⟨j, b, _, hcomm⟩ := ConstructibleStratification.inf_refines_snd sF sG l
        ⟨j, b, hcomm⟩) k
  refine isConstructible_of_isClopen_preimage_strata B X r _ fun k => ?_
  have hpull : ∀ (x : GeometricPoint (r.piece k).obj),
      P _ _ ((etaleStalkPresheafFunctor B (r.piece k).obj (r.piece k).property x
          (Type (u + 1))).map
        ((smallEtaleSheafPullback B (Type (u + 1)) (r.inclusion k)).map φ).hom) ↔
      P _ _ ((etaleStalkPresheafFunctor B X.obj X.property
        (x.map (B.inclusion.map (r.inclusion k))) (Type (u + 1))).map φ.hom) := fun x =>
    property_etaleStalk_map_pullback_iff B (r.inclusion k) φ x P hP
  have hset := preimage_setOf_exists_geometricPoint_liesOver (B.inclusion.map (r.inclusion k))
    (fun t => P _ _ ((etaleStalkPresheafFunctor B X.obj X.property t (Type (u + 1))).map φ.hom))
    _ (property_etaleStalk_map_iff_of_base_eq B X.obj X.property φ P hP) hpull
  exact hset ▸ isClopen_setOf_exists_geometricPoint_property_etaleStalk_map B (r.piece k).obj
    (r.piece k).property _ P hP

/-- A map of sets isomorphic to `m` is `m` conjugated by the two equivalences. -/
private theorem eq_comp_of_map_equiv {A C A' C' : Type*} {m : A → C} {m' : A' → C'}
    (a : A ≃ A') (c : C ≃ C') (h : ∀ z, c (m z) = m' (a z)) : m' = ⇑c ∘ m ∘ ⇑a.symm :=
  funext fun w => by simpa using (h (a.symm w)).symm

/-- Surjectivity is invariant under isomorphism of maps of sets. -/
private theorem surjective_iff_of_map_equiv {A C A' C' : Type*} {m : A → C} {m' : A' → C'}
    (a : A ≃ A') (c : C ≃ C') (h : ∀ z, c (m z) = m' (a z)) :
    Function.Surjective m ↔ Function.Surjective m' := by
  have hm' := eq_comp_of_map_equiv a c h
  rw [hm', Equiv.comp_surjective, Equiv.surjective_comp]

/-- Injectivity is invariant under isomorphism of maps of sets. -/
private theorem injective_iff_of_map_equiv {A C A' C' : Type*} {m : A → C} {m' : A' → C'}
    (a : A ≃ A') (c : C ≃ C') (h : ∀ z, c (m z) = m' (a z)) :
    Function.Injective m ↔ Function.Injective m' := by
  have hm' := eq_comp_of_map_equiv a c h
  rw [hm', Equiv.comp_injective, Equiv.injective_comp]

/-- Having the isomorphism class of a fixed map of sets is invariant under isomorphism of maps of
sets. -/
private theorem isoClass_iff_of_map_equiv {A₀ : Type v} {C₀ : Type w} (m₀ : A₀ → C₀)
    {A C A' C' : Type*} {m : A → C} {m' : A' → C'}
    (a : A ≃ A') (c : C ≃ C') (h : ∀ z, c (m z) = m' (a z)) :
    (∃ (b : A ≃ A₀) (d : C ≃ C₀), ∀ z, d (m z) = m₀ (b z)) ↔
      ∃ (b : A' ≃ A₀) (d : C' ≃ C₀), ∀ z, d (m' z) = m₀ (b z) := by
  have hm' := eq_comp_of_map_equiv a c h
  rw [hm']
  exact ⟨fun ⟨b, d, hbd⟩ =>
      ⟨a.symm.trans b, c.symm.trans d, fun z => by simpa using hbd (a.symm z)⟩,
    fun ⟨b, d, hbd⟩ => ⟨a.trans b, c.trans d, fun z => by simpa using hbd (a z)⟩⟩

/-- **Stacks 09YS, part (1), surjectivity.** Let `X` be a quasi-compact quasi-separated scheme.
For a map of constructible sheaves of sets on the small étale site of `X`, the set of points of
`X` at which the induced map of geometric stalks is surjective is constructible. -/
@[stacks 09YS "part (1), surjectivity"]
public theorem isConstructible_setOf_surjective_etaleStalk_map
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (φ : F ⟶ G)
    (hF : IsConstructibleSetSheaf B X F) (hG : IsConstructibleSetSheaf B X G) :
    IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      Function.Surjective
        ((etaleStalkPresheafFunctor B X.obj X.property t (Type (u + 1))).map φ.hom)} :=
  isConstructible_setOf_exists_geometricPoint_property_etaleStalk_map B X φ hF hG
    (fun _ _ m => Function.Surjective m)
    fun _ _ _ _ _ _ a c h => surjective_iff_of_map_equiv a c h

/-- **Stacks 09YS, part (1), injectivity.** Let `X` be a quasi-compact quasi-separated scheme.
For a map of constructible sheaves of sets on the small étale site of `X`, the set of points of
`X` at which the induced map of geometric stalks is injective is constructible. -/
@[stacks 09YS "part (1), injectivity"]
public theorem isConstructible_setOf_injective_etaleStalk_map
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (φ : F ⟶ G)
    (hF : IsConstructibleSetSheaf B X F) (hG : IsConstructibleSetSheaf B X G) :
    IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      Function.Injective
        ((etaleStalkPresheafFunctor B X.obj X.property t (Type (u + 1))).map φ.hom)} :=
  isConstructible_setOf_exists_geometricPoint_property_etaleStalk_map B X φ hF hG
    (fun _ _ m => Function.Injective m)
    fun _ _ _ _ _ _ a c h => injective_iff_of_map_equiv a c h

/-- **Stacks 09YS, part (1), prescribed isomorphism class.** Let `X` be a quasi-compact
quasi-separated scheme and let `m₀` be a map of sets. For a map of constructible sheaves of sets
on the small étale site of `X`, the set of points of `X` at which the induced map of geometric
stalks is isomorphic to `m₀` is constructible. -/
@[stacks 09YS "part (1), isomorphic to a given map of sets"]
public theorem isConstructible_setOf_etaleStalk_map_iso {A₀ : Type v} {C₀ : Type w}
    (m₀ : A₀ → C₀) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (φ : F ⟶ G)
    (hF : IsConstructibleSetSheaf B X F) (hG : IsConstructibleSetSheaf B X G) :
    IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      ∃ (b : (etaleStalkPresheafFunctor B X.obj X.property t (Type (u + 1))).obj F.obj ≃ A₀)
        (d : (etaleStalkPresheafFunctor B X.obj X.property t (Type (u + 1))).obj G.obj ≃ C₀),
        ∀ z, d ((etaleStalkPresheafFunctor B X.obj X.property t (Type (u + 1))).map φ.hom z) =
          m₀ (b z)} :=
  isConstructible_setOf_exists_geometricPoint_property_etaleStalk_map B X φ hF hG
    (fun _ _ m => ∃ (b : _ ≃ A₀) (d : _ ≃ C₀), ∀ z, d (m z) = m₀ (b z))
    fun _ _ _ _ _ _ a c h => isoClass_iff_of_map_equiv m₀ a c h

end Sets

section Object

universe u₂ v₂

variable (B : BigEtaleSite.{u}) {D : Type u₂} {FD : D → D → Type*} {CD : D → Type v₂}
  [∀ E E', FunLike (FD E E') (CD E) (CD E')] [Category.{v₂} D] [ConcreteCategory.{v₂} D FD]
  [UnivLE.{u, v₂}] [PreservesFilteredColimitsOfSize.{v₂, v₂} (forget D)]
  [(forget D).ReflectsIsomorphisms] [HasColimitsOfSize.{u, u} D]

include FD CD

/-- **The locus of a stalkwise condition on a scheme carrying a locally constant sheaf.** If `F`
is locally constant on the small étale site of `S`, the set of points at which some geometric
stalk of `F` has an isomorphism-invariant property is open and closed: on a covering family
trivializing `F` the condition is read off the constant value. -/
public theorem isClopen_setOf_exists_geometricPoint_property_etaleStalk
    (S : Scheme.{u}) (hS : B.Contains S)
    [∀ V : SmallEtale B S hS, HasWeakSheafify ((SmallEtale.topology B S hS).over V) D]
    [∀ V : SmallEtale B S hS, ((SmallEtale.topology B S hS).over V).WEqualsLocallyBijective D]
    (F : Sheaf (SmallEtale.topology B S hS) D)
    (hF : Stacks.ConstantSheaf.IsLocallyConstant (SmallEtale.topology B S hS) F)
    (R : D → Prop) (hR : ∀ {E E' : D}, (E ≅ E') → (R E ↔ R E')) :
    IsClopen {z : S | ∃ t : GeometricPoint S, t.LiesOver z ∧
      R (etaleStalk B S hS t F.obj)} := by
  classical
  obtain ⟨I, V, cov, hcov, hconst⟩ := hF.exists_cover (SmallEtale.final B S hS)
  choose E hE using fun i => (hconst i).mem_essImage
  have key : ∀ (Q : D → Prop), (∀ {E E' : D}, (E ≅ E') → (Q E ↔ Q E')) → ∀ z : S,
      (∃ t : GeometricPoint S, t.LiesOver z ∧ Q (etaleStalk B S hS t F.obj)) ↔
        ∃ i, Q (E i) ∧ z ∈ Set.range ⇑(B.inclusion.map (V i).obj.hom).base := by
    intro Q hQ z
    constructor
    · rintro ⟨t, htz, hQt⟩
      obtain ⟨i, y, hy⟩ := exists_geometricPointFiber_of_coverFinal B S hS V cov hcov t
      refine ⟨i, ?_, y.1.base default, hy.trans htz⟩
      exact (hQ (Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver
        (geometricPointSitePoint B S hS t) y F (E i) (hE i).some)).mp hQt
    · rintro ⟨i, hQE, v, hv⟩
      obtain ⟨t, y, htz⟩ := exists_geometricPoint_fiber_of_point B S hS (V i) v
      refine ⟨t, hv ▸ htz, ?_⟩
      exact (hQ (Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver
        (geometricPointSitePoint B S hS t) y F (E i) (hE i).some)).mpr hQE
  exact isClopen_setOf_exists_geometricPoint_of_cover
    (fun i => Set.range ⇑(B.inclusion.map (V i).obj.hom).base)
    (fun i => (B.inclusion.map (V i).obj.hom).isOpenMap.isOpen_range)
    (fun t => R (etaleStalk B S hS t F.obj))
    (fun h => hR ((etaleStalkPresheafFunctorIsoOfEqBase B S hS h D).app F.obj))
    (fun i => R (E i)) (key R hR) (key (fun E => ¬ R E) fun e => not_congr (hR e))

variable [HasProducts.{u} D]

/-- **Tag 09YS, parts (2) and (3), for an arbitrary isomorphism-invariant property of the
coefficient objects.** On a quasi-compact quasi-separated scheme, the set of points at which some
geometric stalk of a sheaf which is locally constant on the strata of a constructible
stratification of the whole scheme has such a property is constructible. -/
public theorem isConstructible_setOf_exists_geometricPoint_property_etaleStalk
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      HasWeakSheafify ((SmallEtale.topology B Z.obj Z.property).over V) D]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective D]
    [∀ (Y Z : B.Scheme) (f : Z ⟶ Y),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Z.obj Z.property)).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    (hF : ∃ s : ConstructibleStratification B X ⊤, ∀ k,
      Stacks.ConstantSheaf.IsLocallyConstant
        (SmallEtale.topology B (s.piece k).obj (s.piece k).property)
        (smallEtalePullObj B (s.inclusion k) F))
    (R : D → Prop) (hR : ∀ {E E' : D}, (E ≅ E') → (R E ↔ R E')) :
    IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      R (etaleStalk B X.obj X.property t F.obj)} := by
  obtain ⟨s, hs⟩ := hF
  refine isConstructible_of_isClopen_preimage_strata B X s _ fun k => ?_
  have hpull : ∀ x : GeometricPoint (s.piece k).obj,
      R (etaleStalk B (s.piece k).obj (s.piece k).property x
          (smallEtalePullObj B (s.inclusion k) F).obj) ↔
        R (etaleStalk B X.obj X.property
          (x.map (B.inclusion.map (s.inclusion k))) F.obj) := fun x =>
    hR (etaleStalkSmallEtalePullObjIso B (s.inclusion k) x D F)
  have hset := preimage_setOf_exists_geometricPoint_liesOver (B.inclusion.map (s.inclusion k))
    (fun t => R (etaleStalk B X.obj X.property t F.obj)) _
    (fun h => hR ((etaleStalkPresheafFunctorIsoOfEqBase B X.obj X.property h D).app F.obj)) hpull
  exact hset ▸ isClopen_setOf_exists_geometricPoint_property_etaleStalk B (s.piece k).obj
    (s.piece k).property _ (hs k) R hR

end Object

section Support

universe r

/-- A sheaf of modules which is locally constant with finitely generated values is locally
constant. -/
private theorem isLocallyConstant_of_isFiniteTypeLocallyConstant {C : Type*} [Category C]
    (J : GrothendieckTopology C) (Λ : Type r) [Ring Λ]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} Λ)]
    (F : Sheaf J (ModuleCat.{w} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ J F) :
    Stacks.ConstantSheaf.IsLocallyConstant J F := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hf, hdata⟩ := hF U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨E, -, hiso⟩ := hdata i
  exact ⟨⟨E, hiso⟩⟩

/-- **Stacks 09YS, part (2).** Let `X` be a quasi-compact quasi-separated scheme. The support of
a constructible abelian sheaf on the small étale site of `X` is constructible. -/
@[stacks 09YS "part (2)"]
public theorem isConstructible_supportSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] [UnivLE.{u, w}]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      HasWeakSheafify ((SmallEtale.topology B Z.obj Z.property).over V) AddCommGrpCat.{w}]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective
        AddCommGrpCat.{w}]
    [∀ (Y Z : B.Scheme) (f : Z ⟶ Y),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{w}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Z.obj Z.property)).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w})
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsConstructible (supportSheaf B X.obj X.property F) := by
  have hset : supportSheaf B X.obj X.property F =
      {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
        ¬ IsZero (etaleStalk B X.obj X.property t F.obj)} := by
    ext x
    simp only [mem_supportSheaf_iff_exists, Set.mem_ofPred_eq]
    exact exists_congr fun t => and_congr_right fun _ =>
      not_congr (isZero_etaleStalk_ulift_iff B X.obj X.property F t)
  rw [hset]
  obtain ⟨s, hs⟩ := (isConstructibleFiniteSheaf_iff_exists_stratification B X F).mp hF
  refine isConstructible_setOf_exists_geometricPoint_property_etaleStalk B X F
    ⟨s, fun k => ?_⟩ (fun E => ¬ IsZero E) fun e => not_congr e.isZero_iff
  have := hs k
  infer_instance

/-- **Stacks 09YS, part (3).** Let `X` be a quasi-compact quasi-separated scheme and let `Λ` be a
Noetherian ring. The support of a constructible sheaf of `Λ`-modules on the small étale site of
`X` — the set of points carrying a nonzero geometric stalk — is constructible. -/
@[stacks 09YS "part (3)"]
public theorem isConstructible_support_moduleSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (Λ : Type r) [CommRing Λ]
    [IsNoetherianRing Λ] [UnivLE.{u, w}]
    [PreservesFilteredColimitsOfSize.{max u w, max u w} (forget (ModuleCat.{max u w} Λ))]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      HasWeakSheafify ((SmallEtale.topology B Z.obj Z.property).over V) (ModuleCat.{max u w} Λ)]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective
        (ModuleCat.{max u w} Λ)]
    [∀ (Y Z : B.Scheme) (f : Z ⟶ Y),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max u w} Λ)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Z.obj Z.property)).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max u w} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) :
    IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B X.obj X.property t F.obj)} := by
  obtain ⟨s, hs⟩ := (isConstructibleModuleSheaf_iff_exists_stratification B X Λ F).mp hF
  exact isConstructible_setOf_exists_geometricPoint_property_etaleStalk B X F
    ⟨s, fun k => isLocallyConstant_of_isFiniteTypeLocallyConstant _ Λ _ (hs k)⟩
    (fun E => ¬ IsZero E) fun e => not_congr e.isZero_iff

end Support

end AlgebraicGeometry

end
