module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.DescendedOperations

/-!
# Descending morphism properties across a division of groupoid schemes

Let `F : G ⟶ K` be a morphism of groupoid schemes over `S` whose square of arrow schemes over
the pairs of objects is cartesian,
```
R ------------→ R̄
|               |
(t, s)          (t̄, s̄)
↓               ↓
U × U --q×q--→ Ū × Ū
```
so that `G` is the restriction of `K` along `q = F.mapObjects`.  This is the situation produced
by [Stacks, Tag 04S4]: `Ū = U/P` is the quotient of `U` by a finite locally free subgroupoid and
`K` is the descended groupoid.  What the argument of [Stacks, Tag 04S6] needs at that point is
the passage of data from `G` to `K`, in the direction opposite to base change:

* the source and target of `K` inherit from those of `G` any property which is fppf-local at the
  source and at the target, because `K.source` is covered by `G.source` through the cartesian
  square and `q` is flat, locally of finite presentation and surjective;
* the identity section of `K` is an open immersion as soon as the kernel pair of `q` is carried by
  an open subscheme of the arrow scheme of `G` — which is exactly what the finite locally free
  subgroupoid of the division provides, since it is open in `R`.

Both are descent statements along the single fppf covering `q`, and both are stated here with the
cartesian square as an explicit hypothesis, so that they apply verbatim to the output of
[Stacks, Tag 04S4] without reconstructing the fully faithful evaluation functors.

## Main definitions

This file introduces no definitions.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isPullback_sourceFactor_of_isPullback_arrows`: the factoring
  of `F.mapArrows` through the fibre product `R̄ ×_{s̄, Ū, q} U` is a base change of `q` along the
  target of `G`.  This is the one cartesian square all the transfers below are read off.
* `Stacks.Groupoids.GroupoidScheme.property_mapArrows_of_isPullback_arrows`: the map of arrow
  schemes inherits from the map of object schemes any property stable under base change and
  composition.
* `Stacks.Groupoids.GroupoidScheme.property_source_of_isPullback_arrows`: the source of `K`
  inherits from the source of `G` any property which is fppf-local at the source and at the
  target.
* `Stacks.Groupoids.GroupoidScheme.jointlyMono₂_of_isPullback_arrows`: the target and source of
  `K` are jointly monic as soon as those of `G` are.
* `Stacks.Groupoids.GroupoidScheme.jointlyMono₂_of_isEquivalenceRelation`,
  `Stacks.Groupoids.GroupoidScheme.mono_groupoidPreRelation_of_jointlyMono₂` and
  `Stacks.Groupoids.GroupoidScheme.isEquivalenceRelation_of_jointlyMono₂`: for a groupoid
  scheme, being an internal equivalence relation, having jointly monic target and source, and
  having monomorphic pre-relation are the same thing.
* `Stacks.Groupoids.GroupoidScheme.isPullback_identity_of_isPullback_arrows` and
  `Stacks.Groupoids.GroupoidScheme.isOpenImmersion_identity_of_isPullback_arrows`: an open
  subscheme of the arrow scheme of `G` realizing the kernel pair of `q` is a base change of the
  identity section of `K`, which is therefore an open immersion.

## Implementation notes

The fully faithfulness of the evaluation functors of `F` is a consequence of the cartesian square
(`AlgebraicGeometry.evaluation_fullyFaithful_of_isPullback`) and is the form in which the square
is used in the two statements whose proof is a diagram chase on generalized points: the lifting
property of the cartesian square is applied to a *chosen* preimage arrow, and that is what the
`Functor.FullyFaithful.preimage` of an evaluation functor supplies.

`property_source_of_isPullback_arrows` is the only statement here that needs `q` to be surjective
and flat: locality at the source is applied to the single covering `{R ⟶ R̄ ×_{s̄, Ū, q} U}` and
locality at the target to the single covering `{U ⟶ Ū}`, and both coverings are fppf precisely
because `q` is.  The property is *not* assumed stable under base change: the only base changes
taken are of `q` itself, and they are performed on the covering rather than on the property.

Joint monicity is transferred by a double base change: a pair of generalized arrows of `K` agreeing
after `s̄` and `t̄` is pulled back twice along `q`, where it becomes a pair of arrows of `G` and so
is equal, and the two pullbacks compose to a flat surjection, hence an epimorphism.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 046S](https://stacks.math.columbia.edu/tag/046S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} {G K : GroupoidScheme S}

/-- A base change in `Over S` of a flat surjective morphism is flat and surjective. -/
private theorem surjective_and_flat_of_isPullback {A B C D : Over S} {fst : A ⟶ B} {snd : A ⟶ C}
    {f : B ⟶ D} {g : C ⟶ D} (h : IsPullback fst snd f g) [Surjective f.left] [Flat f.left] :
    Surjective snd.left ∧ Flat snd.left :=
  ⟨MorphismProperty.of_isPullback (P := @Surjective) (h.map (Over.forget S)) ‹_›,
    MorphismProperty.of_isPullback (P := @Flat) (h.map (Over.forget S)) ‹_›⟩

/-- The arrow map of a morphism of groupoid schemes with cartesian arrow square, factored
through the fibre product of the source of `K` with the object map, is a base change of the
object map along the target of `G`.

Every transfer of a morphism property from `G` to `K` below is read off this square. -/
theorem isPullback_sourceFactor_of_isPullback_arrows (F : Hom G K)
    (hp : IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K)
      (prod.map F.mapObjects F.mapObjects)) :
    IsPullback G.target
      (pullback.lift (f := K.source) (g := F.mapObjects) F.mapArrows G.source F.map_source)
      F.mapObjects (pullback.fst K.source F.mapObjects ≫ K.target) := by
  have hq := hp.flip
  have hjGfst : groupoidPreRelation G ≫ prod.fst = G.target := prod.lift_fst _ _
  have hjGsnd : groupoidPreRelation G ≫ prod.snd = G.source := prod.lift_snd _ _
  have hjKfst : groupoidPreRelation K ≫ prod.fst = K.target := prod.lift_fst _ _
  have hjKsnd : groupoidPreRelation K ≫ prod.snd = K.source := prod.lift_snd _ _
  have hfst : (pullback.lift (f := K.source) (g := F.mapObjects) F.mapArrows G.source
      F.map_source) ≫ pullback.fst K.source F.mapObjects = F.mapArrows :=
    pullback.lift_fst _ _ _
  have hsnd : (pullback.lift (f := K.source) (g := F.mapObjects) F.mapArrows G.source
      F.map_source) ≫ pullback.snd K.source F.mapObjects = G.source :=
    pullback.lift_snd _ _ _
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← Category.assoc, hfst, F.map_target]
  · intro T a b ht hab
    have hs : a ≫ G.source = b ≫ G.source := by
      rw [← hsnd, ← Category.assoc, ← Category.assoc, hab]
    have hr : a ≫ F.mapArrows = b ≫ F.mapArrows := by
      rw [← hfst, ← Category.assoc, ← Category.assoc, hab]
    refine hq.hom_ext (prod.hom_ext ?_ ?_) hr
    · rwa [Category.assoc, Category.assoc, hjGfst]
    · rwa [Category.assoc, Category.assoc, hjGsnd]
  · intro T t v htv
    have hw : prod.lift t (v ≫ pullback.snd K.source F.mapObjects) ≫
        prod.map F.mapObjects F.mapObjects =
        (v ≫ pullback.fst K.source F.mapObjects) ≫ groupoidPreRelation K := by
      refine prod.hom_ext ?_ ?_
      · simpa only [Category.assoc, prod.map_fst, prod.lift_fst_assoc, hjKfst] using htv
      · simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc, hjKsnd,
          pullback.condition]
    refine ⟨hq.lift (prod.lift t (v ≫ pullback.snd K.source F.mapObjects))
      (v ≫ pullback.fst K.source F.mapObjects) hw, ?_, ?_⟩
    · have h := congrArg (fun f => f ≫ prod.fst)
        (hq.lift_fst (prod.lift t (v ≫ pullback.snd K.source F.mapObjects))
          (v ≫ pullback.fst K.source F.mapObjects) hw)
      rwa [Category.assoc, hjGfst, prod.lift_fst] at h
    · have hsrc := congrArg (fun f => f ≫ prod.snd)
        (hq.lift_fst (prod.lift t (v ≫ pullback.snd K.source F.mapObjects))
          (v ≫ pullback.fst K.source F.mapObjects) hw)
      rw [Category.assoc, hjGsnd, prod.lift_snd] at hsrc
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hfst]
        exact hq.lift_snd (prod.lift t (v ≫ pullback.snd K.source F.mapObjects))
          (v ≫ pullback.fst K.source F.mapObjects) hw
      · rwa [Category.assoc, hsnd]

/-- The map of arrow schemes of a morphism of groupoid schemes with cartesian arrow square
inherits from the map of object schemes every property stable under base change and under
composition. -/
theorem property_mapArrows_of_isPullback_arrows (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] (F : Hom G K)
    (hp : IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K)
      (prod.map F.mapObjects F.mapObjects))
    (h : P F.mapObjects.left) : P F.mapArrows.left := by
  have ha : P (pullback.lift (f := K.source) (g := F.mapObjects) F.mapArrows G.source
      F.map_source).left :=
    P.of_isPullback ((isPullback_sourceFactor_of_isPullback_arrows F hp).map
      (Over.forget S)) h
  have hb : P (pullback.fst K.source F.mapObjects).left :=
    P.of_isPullback ((IsPullback.of_hasPullback K.source F.mapObjects).map
      (Over.forget S)).flip h
  have he : (pullback.lift (f := K.source) (g := F.mapObjects) F.mapArrows G.source
      F.map_source).left ≫ (pullback.fst K.source F.mapObjects).left = F.mapArrows.left :=
    congrArg Over.Hom.left (pullback.lift_fst _ _ _)
  exact he ▸ P.comp_mem _ _ ha hb

/-- The source of `K` inherits from the source of `G` every property which is local at the
source and at the target for the fppf precoverage, when the map of object schemes is
surjective, flat and locally of finite presentation and the arrow square is cartesian.

Both localities are applied to a single covering: at the source to the factoring of
`F.mapArrows` through `R̄ ×_{s̄, Ū, q} U`, which is a base change of `q` by
`Stacks.Groupoids.GroupoidScheme.isPullback_sourceFactor_of_isPullback_arrows`, and at the
target to `q` itself. -/
theorem property_source_of_isPullback_arrows (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.fppfPrecoverage] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (F : Hom G K)
    (hp : IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K)
      (prod.map F.mapObjects F.mapObjects))
    [Surjective F.mapObjects.left] [Flat F.mapObjects.left]
    [LocallyOfFinitePresentation F.mapObjects.left]
    (hs : P G.source.left) : P K.source.left := by
  set a := pullback.lift (f := K.source) (g := F.mapObjects) F.mapArrows G.source F.map_source
    with ha
  have hsq := isPullback_sourceFactor_of_isPullback_arrows F hp
  obtain ⟨_, _⟩ := surjective_and_flat_of_isPullback hsq
  have _ : LocallyOfFinitePresentation a.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (hsq.map (Over.forget S))
      (inferInstance : LocallyOfFinitePresentation F.mapObjects.left)
  have hlocal : P (pullback.snd K.source F.mapObjects).left := by
    refine MorphismProperty.IsLocalAtSource.of_forall_comp
      (P := P) a.left.singleton_mem_fppfPrecoverage ?_
    rintro _ _ ⟨⟩
    show P ((a ≫ pullback.snd K.source F.mapObjects).left)
    simpa only [ha, pullback.lift_snd] using hs
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := P) F.mapObjects.left.singleton_mem_fppfPrecoverage ?_
  rintro _ _ _ ⟨⟩
  have hpb : IsPullback (pullback.fst K.source F.mapObjects).left
      (pullback.snd K.source F.mapObjects).left K.source.left F.mapObjects.left :=
    (IsPullback.of_hasPullback K.source F.mapObjects).map (Over.forget S)
  rw [← hpb.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp P hpb.isoPullback.inv _ hlocal

/-- The target and the source of `K` are jointly monic as soon as those of `G` are, when the
map of object schemes is flat and surjective and the arrow square is cartesian.

A pair of generalized arrows of `K` agreeing after the target and after the source is pulled
back twice along the object map, where the cartesian square turns it into a pair of generalized
arrows of `G`; the two pullbacks compose to a flat surjection, hence to an epimorphism. -/
theorem jointlyMono₂_of_isPullback_arrows [JointlyMono₂ G.target G.source] (F : Hom G K)
    (hp : IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K)
      (prod.map F.mapObjects F.mapObjects))
    [Surjective F.mapObjects.left] [Flat F.mapObjects.left] :
    JointlyMono₂ K.target K.source := by
  classical
  have hff := fun T => AlgebraicGeometry.evaluation_fullyFaithful_of_isPullback F hp T
  constructor
  intro T r₁ r₂ ht hs
  set f : pullback F.mapObjects (r₁ ≫ K.source) ⟶ T :=
    pullback.snd F.mapObjects (r₁ ≫ K.source) with hf
  set g : pullback F.mapObjects (f ≫ r₁ ≫ K.target) ⟶ pullback F.mapObjects (r₁ ≫ K.source) :=
    pullback.snd F.mapObjects (f ≫ r₁ ≫ K.target) with hg
  set c := g ≫ f with hc
  set x : G.Evaluation (pullback F.mapObjects (f ≫ r₁ ≫ K.target)) :=
    g ≫ pullback.fst F.mapObjects (r₁ ≫ K.source) with hx0
  set y : G.Evaluation (pullback F.mapObjects (f ≫ r₁ ≫ K.target)) :=
    pullback.fst F.mapObjects (f ≫ r₁ ≫ K.target) with hy0
  have hx : x ≫ F.mapObjects = c ≫ r₁ ≫ K.source := by
    simp only [hx0, hc, hf, Category.assoc, pullback.condition]
  have hy : y ≫ F.mapObjects = c ≫ r₁ ≫ K.target := by
    simpa only [hy0, hc, hg, Category.assoc] using
      (pullback.condition (f := F.mapObjects) (g := f ≫ r₁ ≫ K.target))
  let a : K.EvaluationHom ((F.evaluation _).obj x) ((F.evaluation _).obj y) :=
    { arrow := c ≫ r₁
      source_eq := by
        show (c ≫ r₁) ≫ K.source = x ≫ F.mapObjects
        simpa only [Category.assoc] using hx.symm
      target_eq := by
        show (c ≫ r₁) ≫ K.target = y ≫ F.mapObjects
        simpa only [Category.assoc] using hy.symm }
  let b : K.EvaluationHom ((F.evaluation _).obj x) ((F.evaluation _).obj y) :=
    { arrow := c ≫ r₂
      source_eq := by
        show (c ≫ r₂) ≫ K.source = x ≫ F.mapObjects
        rw [Category.assoc, ← hs, hx]
      target_eq := by
        show (c ≫ r₂) ≫ K.target = y ≫ F.mapObjects
        rw [Category.assoc, ← ht, hy] }
  have he : (hff _).some.preimage a = (hff _).some.preimage b :=
    EvaluationHom.ext (JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source) _ _
      (((hff _).some.preimage a).target_eq.trans ((hff _).some.preimage b).target_eq.symm)
      (((hff _).some.preimage a).source_eq.trans ((hff _).some.preimage b).source_eq.symm))
  have he' : a = b := by
    rw [← (hff _).some.map_preimage a, ← (hff _).some.map_preimage b, he]
  have hc' := fun {X : Over S} (k : X ⟶ K.objects) =>
    surjective_and_flat_of_isPullback (IsPullback.of_hasPullback F.mapObjects k)
  obtain ⟨_, _⟩ := hc' (r₁ ≫ K.source)
  obtain ⟨_, _⟩ := hc' (f ≫ r₁ ≫ K.target)
  have _ : Epi c.left := Flat.epi_of_flat_of_surjective (g.left ≫ f.left)
  exact Over.OverMorphism.ext
    ((cancel_epi c.left).mp (congrArg Over.Hom.left (congrArg EvaluationHom.arrow he')))

/-- An open — or indeed any — subscheme of the arrow scheme of `G` realizing the kernel pair of
the object map is a base change of the identity section of `K` along that map.

The hypothesis is that `q : P ⟶ R` has target `t` and source `s` whose square over the object
map is cartesian: `P = U ×_{Ū} U`.  Then `P ⟶ R ⟶ R̄` is the base change of `ē : Ū ⟶ R̄` along
`U ⟶ Ū`. -/
theorem isPullback_identity_of_isPullback_arrows [JointlyMono₂ G.target G.source] (F : Hom G K)
    (hp : IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K)
      (prod.map F.mapObjects F.mapObjects))
    {P : Over S} (q : P ⟶ G.arrows) (t s : P ⟶ G.objects)
    (hqt : q ≫ G.target = t) (hqs : q ≫ G.source = s)
    (hkp : IsPullback t s F.mapObjects F.mapObjects) :
    IsPullback q (s ≫ F.mapObjects) F.mapArrows K.identity := by
  classical
  have hff := fun T => AlgebraicGeometry.evaluation_fullyFaithful_of_isPullback F hp T
  have hw : q ≫ F.mapArrows = (s ≫ F.mapObjects) ≫ K.identity := by
    let r : K.EvaluationHom ((F.evaluation P).obj s) ((F.evaluation P).obj t) :=
      { arrow := (s ≫ F.mapObjects) ≫ K.identity
        source_eq := by
          show (s ≫ F.mapObjects) ≫ K.identity ≫ K.source = s ≫ F.mapObjects
          simp only [K.source_identity, Category.comp_id]
        target_eq := by
          show (s ≫ F.mapObjects) ≫ K.identity ≫ K.target = t ≫ F.mapObjects
          simpa only [K.target_identity, Category.comp_id] using hkp.w.symm }
    let p := (hff P).some.preimage r
    have he : p.arrow = q := JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source)
      _ _ (p.target_eq.trans hqt.symm) (p.source_eq.trans hqs.symm)
    rw [← he]
    exact congrArg EvaluationHom.arrow ((hff P).some.map_preimage r)
  refine IsPullback.mk' hw ?_ ?_
  · intro T a b h _
    refine hkp.hom_ext ?_ ?_
    · rw [← hqt, ← Category.assoc, ← Category.assoc, h]
    · rw [← hqs, ← Category.assoc, ← Category.assoc, h]
  · intro T r u hru
    have hs : (r ≫ G.source) ≫ F.mapObjects = u := by
      rw [Category.assoc, ← F.map_source, ← Category.assoc, hru,
        Category.assoc, K.source_identity, Category.comp_id]
    have ht : (r ≫ G.target) ≫ F.mapObjects = u := by
      rw [Category.assoc, ← F.map_target, ← Category.assoc, hru,
        Category.assoc, K.target_identity, Category.comp_id]
    refine ⟨hkp.lift (r ≫ G.target) (r ≫ G.source) (ht.trans hs.symm), ?_, ?_⟩
    · apply JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source)
      · rw [Category.assoc, hqt]
        exact hkp.lift_fst _ _ _
      · rw [Category.assoc, hqs]
        exact hkp.lift_snd _ _ _
    · rwa [← Category.assoc, hkp.lift_snd]

/-- **The identity section of the divided groupoid is an open immersion.**

If the kernel pair of the object map is realized by an open subscheme of the arrow scheme of
`G`, then the identity section of `K` is an open immersion: by
`Stacks.Groupoids.GroupoidScheme.isPullback_identity_of_isPullback_arrows` it is the descent of
that open immersion along the map of arrow schemes, which is surjective, flat and quasi-compact
because the map of object schemes is.

This is the input of `Stacks.Groupoids.GroupoidScheme.etale_source_of_isOpenImmersion_identity`,
and the step of [Stacks, Tag 04S6] which turns the division of [Stacks, Tag 04S4] into
étaleness of the descended source and target. -/
theorem isOpenImmersion_identity_of_isPullback_arrows [JointlyMono₂ G.target G.source]
    (F : Hom G K)
    (hp : IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K)
      (prod.map F.mapObjects F.mapObjects))
    [Surjective F.mapObjects.left] [Flat F.mapObjects.left] [QuasiCompact F.mapObjects.left]
    {P : Over S} (q : P ⟶ G.arrows) (t s : P ⟶ G.objects)
    (hqt : q ≫ G.target = t) (hqs : q ≫ G.source = s)
    (hkp : IsPullback t s F.mapObjects F.mapObjects) [IsOpenImmersion q.left] :
    IsOpenImmersion K.identity.left := by
  have _ : MorphismProperty.IsStableUnderComposition
      (@Surjective : MorphismProperty Scheme.{u}) := ⟨fun _ _ _ _ => inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((isPullback_identity_of_isPullback_arrows F hp q t s hqt hqs hkp).map (Over.forget S))
    ⟨⟨property_mapArrows_of_isPullback_arrows @Surjective F hp inferInstance,
      property_mapArrows_of_isPullback_arrows @Flat F hp inferInstance⟩,
      property_mapArrows_of_isPullback_arrows @QuasiCompact F hp inferInstance⟩
    (show IsOpenImmersion q.left from inferInstance)

/-! ### Joint monicity and the internal equivalence relation -/

/-- The target and source of a groupoid scheme which form an internal equivalence relation are
jointly monic: joint monicity is one of the clauses of an equivalence relation. -/
theorem jointlyMono₂_of_isEquivalenceRelation (G : GroupoidScheme S)
    [CategoryTheory.IsEquivalenceRelation G.target G.source] :
    JointlyMono₂ G.target G.source :=
  CategoryTheory.IsEquivalenceRelation.nonempty_equivalenceRelation.some.toJointlyMono₂

/-- A groupoid scheme whose target and source are jointly monic has monomorphic pre-relation:
the two projections of the pre-relation are the target and the source. -/
theorem mono_groupoidPreRelation_of_jointlyMono₂ (G : GroupoidScheme S)
    [JointlyMono₂ G.target G.source] : Mono (groupoidPreRelation G) := by
  have hfst : groupoidPreRelation G ≫ prod.fst = G.target := prod.lift_fst _ _
  have hsnd : groupoidPreRelation G ≫ prod.snd = G.source := prod.lift_snd _ _
  constructor
  intro T a b hab
  refine JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source) a b ?_ ?_
  · rw [← hfst, ← Category.assoc, ← Category.assoc, hab]
  · rw [← hsnd, ← Category.assoc, ← Category.assoc, hab]

/-- **A groupoid scheme whose target and source are jointly monic is an internal equivalence
relation.**  Reflexivity, symmetry and transitivity on generalized points are the groupoid
axioms (`AlgebraicGeometry.groupoidPreRelation_isPreEquivalenceRelation`); joint monicity is the
remaining clause. -/
theorem isEquivalenceRelation_of_jointlyMono₂ (G : GroupoidScheme S)
    [JointlyMono₂ G.target G.source] :
    CategoryTheory.IsEquivalenceRelation G.target G.source := by
  have h := (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    (groupoidPreRelation G)).2
    ⟨mono_groupoidPreRelation_of_jointlyMono₂ G,
      AlgebraicGeometry.groupoidPreRelation_isPreEquivalenceRelation G⟩
  rwa [show (groupoidPreRelation G).target = G.target from prod.lift_fst _ _,
    show (groupoidPreRelation G).source = G.source from prod.lift_snd _ _] at h

end Stacks.Groupoids.GroupoidScheme

end
