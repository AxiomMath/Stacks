module

public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Evaluation

/-!
# Descending the structure morphisms of a groupoid scheme along a quotient of its objects

Let `G = (U, R, s, t, c)` be a groupoid scheme over `S`, let `q : U ⟶ Q` and `r : R ⟶ A` be
morphisms and let `s', t' : A ⟶ Q` be such that the square

```
R ----r----> A
|            |
j = (t,s)   (t',s')
|            |
v            v
U ×_S U --> Q ×_S Q
```

is cartesian, `q` being an fppf covering on its own.  Then the identity, the inverse and the
composition of `G` descend to `A` as soon as they are invariant, and `(Q, A, s', t', c')` is a
groupoid scheme of which `G` is the restriction along `q`: the square above is the square of
arrow schemes of a morphism of groupoid schemes, so `G` is the full subgroupoid induced along `q`
on every test scheme.

This is the second half of the fourth conclusion of Tag 04S4: the first half produces `A` and
`r` by descending the arrow scheme, and this file turns them into a groupoid.

## Main definitions

* `AlgebraicGeometry.SingletonCover` is the property of a single morphism of generating a
  covering sieve.
* `AlgebraicGeometry.DescendedOperations` records the three descended structure morphisms with
  the identities expressing that they descend those of `G`.

## Main results

* `AlgebraicGeometry.evaluation_fullyFaithful_of_isPullback`: **a morphism of groupoid schemes
  whose square of arrow schemes over the pairs of objects is cartesian is fully faithful on the
  generalized points of every test scheme**, that is, exhibits its source as the restriction of
  its target.
* `AlgebraicGeometry.exists_local_arrow`, `AlgebraicGeometry.exists_local_pair` and
  `AlgebraicGeometry.exists_local_triple`: a generalized point of `A`, a composable pair of
  them, or a composable triple, lifts to `R` after a covering of the test object.
* `AlgebraicGeometry.exists_descendedOperations`: **the three structure morphisms descend.**
* `AlgebraicGeometry.DescendedOperations.exists_groupoid`: **the descended data form a groupoid
  scheme on `Q`, and `G` is its restriction along `q`**: the square of arrow schemes over the
  pairs of objects is cartesian, and so `G` is fully faithful on generalized points.

## Implementation notes

Nothing here uses descent of schemes: `q` is an effective epimorphism because the topology is
subcanonical, and so are `r` and the induced map on composable pairs, because a point of `A`,
a composable pair of them or a composable triple lifts to `R` locally — which is where the
cartesian square is used.  Each descended morphism is then
`CategoryTheory.EffectiveEpi.desc` of the corresponding morphism of `G`, and each of the eleven
groupoid axioms is checked after pulling back along a covering on which the points involved come
from `R`, where it is the corresponding axiom of `G`.

The invariance hypotheses of `AlgebraicGeometry.exists_descendedOperations` are exactly what the
quotient has to supply: two identity arrows with the same image in `Q` have the same image in
`A`, and two arrows with the same image in `A` have inverses, and composites with a second such
pair, with the same image in `A`.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- If the square of arrow schemes `R → A` over `U ×_S U → Q ×_S Q` is cartesian, two arrows
between the same generalized points of `G` are equal as soon as their images in `A` are. -/
lemma evaluationHom_eq_of_image_eq {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {T : Over S} {x y : G.Evaluation T} (a b : x ⟶ y)
    (h : a.arrow ≫ r = b.arrow ≫ r) : a = b := by
  apply GroupoidScheme.EvaluationHom.ext
  apply hp.hom_ext h
  apply prod.hom_ext
  · simpa using a.target_eq.trans b.target_eq.symm
  · simpa using a.source_eq.trans b.source_eq.symm

/-- In the cartesian square of arrow schemes, `r` carries the source of `G` to `s`. -/
private lemma comp_source_eq_of_isPullback {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q)) :
    r ≫ s = G.source ≫ q := by
  simpa using congrArg (· ≫ prod.snd) hp.w

/-- In the cartesian square of arrow schemes, `r` carries the target of `G` to `t`. -/
private lemma comp_target_eq_of_isPullback {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q)) :
    r ≫ t = G.target ≫ q := by
  simpa using congrArg (· ≫ prod.fst) hp.w

/-- A morphism of groupoid schemes whose square of arrow schemes over the pairs of objects is
cartesian is fully faithful on the groupoid of `T`-valued points, for every test scheme `T`. -/
lemma evaluation_fullyFaithful_of_isPullback {S : Scheme.{u}}
    {G H : GroupoidScheme S} (F : GroupoidScheme.Hom G H)
    (h : IsPullback F.mapArrows (prod.lift G.target G.source)
      (prod.lift H.target H.source) (prod.map F.mapObjects F.mapObjects))
    (T : Over S) : Nonempty (F.evaluation T).FullyFaithful := by
  have : (F.evaluation T).Full := ⟨by
    intro x y a
    have w : a.arrow ≫ prod.lift H.target H.source =
        prod.lift y x ≫ prod.map F.mapObjects F.mapObjects := by
      apply prod.hom_ext
      · simpa [GroupoidScheme.Hom.evaluation] using a.target_eq
      · simpa [GroupoidScheme.Hom.evaluation] using a.source_eq
    refine ⟨⟨h.lift a.arrow (prod.lift y x) w, ?_, ?_⟩,
      GroupoidScheme.EvaluationHom.ext (h.lift_fst _ _ _)⟩
    · simpa using congrArg (· ≫ prod.snd) (h.lift_snd a.arrow (prod.lift y x) w)
    · simpa using congrArg (· ≫ prod.fst) (h.lift_snd a.arrow (prod.lift y x) w)⟩
  have : (F.evaluation T).Faithful := ⟨fun {_ _} a b hab =>
    evaluationHom_eq_of_image_eq h a b (congrArg GroupoidScheme.EvaluationHom.arrow hab)⟩
  exact ⟨Functor.FullyFaithful.ofFullyFaithful (F.evaluation T)⟩

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-- A morphism `f : X ⟶ Y` is a singleton cover for `J` if the sieve on `Y` generated by `f`
alone is `J`-covering. -/
abbrev SingletonCover {C : Type*} [Category C] (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y) : Prop := Sieve.generateSingleton f ∈ J Y

/-- The identity of any object is a singleton cover. -/
lemma singletonCover_id {C : Type*} [Category C] (J : GrothendieckTopology C)
    (X : C) : SingletonCover J (𝟙 X) := by
  rw [SingletonCover, ← Sieve.generateSingleton_eq]
  simp

/-- The composite of two singleton covers is a singleton cover. -/
lemma SingletonCover.comp {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : SingletonCover J f) (hg : SingletonCover J g) : SingletonCover J (f ≫ g) := by
  apply J.transitive hg
  rintro T a ⟨b, rfl⟩
  rw [Sieve.pullback_comp]
  apply J.pullback_stable b
  apply J.superset_covering _ hf
  rintro T a ⟨b, rfl⟩
  exact ⟨b, (Category.assoc _ _ _).symm⟩

/-- If `f ≫ g` is a singleton cover, then so is `g`. -/
lemma SingletonCover.of_comp {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : SingletonCover J (f ≫ g)) : SingletonCover J g := by
  apply J.superset_covering _ h
  rintro T a ⟨b, rfl⟩
  exact ⟨b ≫ f, Category.assoc _ _ _⟩

/-- The base change `pullback.snd f g` of a singleton cover `f` along any `g` is a singleton
cover. -/
lemma SingletonCover.pullback {C : Type*} [Category C] [HasPullbacks C]
    {J : GrothendieckTopology C} {X Y Z : C} {f : X ⟶ Z}
    (hf : SingletonCover J f) (g : Y ⟶ Z) : SingletonCover J (pullback.snd f g) := by
  have he : Sieve.generateSingleton (pullback.snd f g) =
      (Sieve.generateSingleton f).pullback g := by
    ext T a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b ≫ pullback.fst f g, by simp [Category.assoc, pullback.condition]⟩
    · rintro ⟨b, h⟩
      exact ⟨pullback.lift b a h, pullback.lift_snd _ _ _⟩
  rw [SingletonCover, he]
  exact J.pullback_stable g hf

/-- For a subcanonical topology, a singleton cover is an effective epimorphism. -/
lemma SingletonCover.effectiveEpi {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.Subcanonical] {X Y : C} {f : X ⟶ Y}
    (hf : SingletonCover J f) : EffectiveEpi f := by
  apply (Sieve.effectiveEpimorphic_singleton f).mp
  apply (Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda _).mpr
  intro Z
  apply (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := J) (P := yoneda.obj Z)).isSheafFor
  rwa [Sieve.generateSingleton_eq]

/-- If `q : U ⟶ Q` is a singleton cover, then any finite list of morphisms `T ⟶ Q` lifts
simultaneously through `q` after precomposition with a singleton cover `W ⟶ T`. -/
lemma exists_local_lifts {C : Type*} [Category C] [HasPullbacks C]
    {J : GrothendieckTopology C} {U Q : C} {q : U ⟶ Q} (hq : SingletonCover J q)
    {T : C} (xs : List (T ⟶ Q)) :
    ∃ (W : C) (p : W ⟶ T), SingletonCover J p ∧
      ∀ x ∈ xs, ∃ y : W ⟶ U, y ≫ q = p ≫ x := by
  induction xs with
  | nil => exact ⟨T, 𝟙 T, singletonCover_id J T, by simp⟩
  | cons x xs ih =>
    obtain ⟨W, p, hp, h⟩ := ih
    refine ⟨pullback q (p ≫ x), pullback.snd q (p ≫ x) ≫ p,
      (hq.pullback (p ≫ x)).comp hp, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨pullback.fst _ _, by simp [Category.assoc, pullback.condition]⟩
    · obtain ⟨y, hy⟩ := h z hz
      exact ⟨pullback.snd _ _ ≫ y, by simp [Category.assoc, hy]⟩

/-- Given the cartesian square of arrow schemes, a point `a : T ⟶ A` together with points `x, y`
of `U` lying over `a ≫ s` and `a ≫ t` lifts to an arrow `b : T ⟶ R` with source `x`, target `y`
and image `a`. -/
lemma exists_arrow_of_endpoints {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {T : Over S} (a : T ⟶ A) (x y : T ⟶ G.objects)
    (hs : x ≫ q = a ≫ s) (ht : y ≫ q = a ≫ t) :
    ∃ b : T ⟶ G.arrows, b ≫ G.source = x ∧ b ≫ G.target = y ∧ b ≫ r = a := by
  have hw : a ≫ prod.lift t s = prod.lift y x ≫ prod.map q q := by
    apply prod.hom_ext <;> simp [hs, ht]
  refine ⟨hp.lift a (prod.lift y x) hw, ?_, ?_, hp.lift_fst _ _ _⟩
  · simpa using congrArg (· ≫ prod.snd) (hp.lift_snd a (prod.lift y x) hw)
  · simpa using congrArg (· ≫ prod.fst) (hp.lift_snd a (prod.lift y x) hw)

/-- Given the cartesian square of arrow schemes and a singleton cover `q`, every point
`a : T ⟶ A` lifts to `R` after precomposition with a singleton cover `W ⟶ T`. -/
lemma exists_local_arrow {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} (hq : SingletonCover J q)
    {T : Over S} (a : T ⟶ A) :
    ∃ (W : Over S) (p : W ⟶ T) (b : W ⟶ G.arrows),
      SingletonCover J p ∧ b ≫ r = p ≫ a := by
  obtain ⟨W, p, hp', h⟩ := exists_local_lifts hq [a ≫ s, a ≫ t]
  obtain ⟨x, hx⟩ := h (a ≫ s) (by simp)
  obtain ⟨y, hy⟩ := h (a ≫ t) (by simp)
  obtain ⟨b, _, _, hb⟩ := exists_arrow_of_endpoints hp (p ≫ a) x y
    (by simpa only [Category.assoc] using hx) (by simpa only [Category.assoc] using hy)
  exact ⟨W, p, b, hp', hb⟩

/-- Given the cartesian square of arrow schemes and a singleton cover `q`, every composable pair
of points `a, b : T ⟶ A` lifts to a composable pair of arrows of `G` after precomposition with a
singleton cover `W ⟶ T`. -/
lemma exists_local_pair {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} (hq : SingletonCover J q)
    {T : Over S} (a b : T ⟶ A) (w : a ≫ s = b ≫ t) :
    ∃ (W : Over S) (p : W ⟶ T) (f g : W ⟶ G.arrows),
      SingletonCover J p ∧ f ≫ G.source = g ≫ G.target ∧
        f ≫ r = p ≫ a ∧ g ≫ r = p ≫ b := by
  obtain ⟨W, p, hp', h⟩ := exists_local_lifts hq [b ≫ s, a ≫ s, a ≫ t]
  obtain ⟨x, hx⟩ := h (b ≫ s) (by simp)
  obtain ⟨y, hy⟩ := h (a ≫ s) (by simp)
  obtain ⟨z, hz⟩ := h (a ≫ t) (by simp)
  obtain ⟨f, fs, ft, fr⟩ := exists_arrow_of_endpoints hp (p ≫ a) y z
    (by simpa only [Category.assoc] using hy) (by simpa only [Category.assoc] using hz)
  obtain ⟨g, gs, gt, gr⟩ := exists_arrow_of_endpoints hp (p ≫ b) x y
    (by simpa only [Category.assoc] using hx) (by simpa only [Category.assoc, w] using hy)
  exact ⟨W, p, f, g, hp', fs.trans gt.symm, fr, gr⟩

/-- Given the cartesian square of arrow schemes and a singleton cover `q`, every composable
triple of points `a, b, c : T ⟶ A` lifts to a composable triple of arrows of `G` after
precomposition with a singleton cover `W ⟶ T`. -/
lemma exists_local_triple {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} (hq : SingletonCover J q)
    {T : Over S} (a b c : T ⟶ A) (w : a ≫ s = b ≫ t) (w' : b ≫ s = c ≫ t) :
    ∃ (W : Over S) (p : W ⟶ T) (f g h : W ⟶ G.arrows),
      SingletonCover J p ∧ f ≫ G.source = g ≫ G.target ∧
        g ≫ G.source = h ≫ G.target ∧
        f ≫ r = p ≫ a ∧ g ≫ r = p ≫ b ∧ h ≫ r = p ≫ c := by
  obtain ⟨W, p, hp', hl⟩ := exists_local_lifts hq [c ≫ s, b ≫ s, a ≫ s, a ≫ t]
  obtain ⟨x, hx⟩ := hl (c ≫ s) (by simp)
  obtain ⟨y, hy⟩ := hl (b ≫ s) (by simp)
  obtain ⟨z, hz⟩ := hl (a ≫ s) (by simp)
  obtain ⟨v, hv⟩ := hl (a ≫ t) (by simp)
  obtain ⟨f, fs, ft, fr⟩ := exists_arrow_of_endpoints hp (p ≫ a) z v
    (by simpa only [Category.assoc] using hz) (by simpa only [Category.assoc] using hv)
  obtain ⟨g, gs, gt, gr⟩ := exists_arrow_of_endpoints hp (p ≫ b) y z
    (by simpa only [Category.assoc] using hy) (by simpa only [Category.assoc, w] using hz)
  obtain ⟨h, hs, ht, hr⟩ := exists_arrow_of_endpoints hp (p ≫ c) x y
    (by simpa only [Category.assoc] using hx) (by simpa only [Category.assoc, w'] using hy)
  exact ⟨W, p, f, g, h, hp', fs.trans gt.symm, gs.trans ht.symm, fr, gr, hr⟩

/-- Morphisms `Q ⟶ A`, `A ⟶ A` and `A ×_{s,Q,t} A ⟶ A` through which `q` and `r` carry the
identity, the inverse and the composition of `G`. -/
structure DescendedOperations {S : Scheme.{u}} (G : GroupoidScheme S)
    {Q A : Over S} (q : G.objects ⟶ Q) (r : G.arrows ⟶ A) (s t : A ⟶ Q) where
  /-- The descended identity. -/
  identity : Q ⟶ A
  /-- The descended inverse. -/
  inverse : A ⟶ A
  /-- The descended composition. -/
  comp : pullback s t ⟶ A
  identity_map : q ≫ identity = G.identity ≫ r
  inverse_map : r ≫ inverse = G.inverse ≫ r
  comp_map : ∀ {T : Over S} (f g : T ⟶ G.arrows)
    (w : f ≫ G.source = g ≫ G.target) (w' : (f ≫ r) ≫ s = (g ≫ r) ≫ t),
    G.compose f g w ≫ r = pullback.lift (f ≫ r) (g ≫ r) w' ≫ comp

/-- Given the cartesian square of arrow schemes and a singleton cover `q` for a subcanonical
topology, if the identity, the inverse and the composition of `G` are invariant under `q` and `r`,
then they descend to `Q` and `A`. -/
lemma exists_descendedOperations {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} (q : G.objects ⟶ Q) (r : G.arrows ⟶ A) (s t : A ⟶ Q)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q)
    (hident : ∀ {T : Over S} (x y : T ⟶ G.objects), x ≫ q = y ≫ q →
      x ≫ G.identity ≫ r = y ≫ G.identity ≫ r)
    (hinv : ∀ {T : Over S} (a b : T ⟶ G.arrows), a ≫ r = b ≫ r →
      a ≫ G.inverse ≫ r = b ≫ G.inverse ≫ r)
    (hcomp : ∀ {T : Over S} (a b c d : T ⟶ G.arrows)
      (w : a ≫ G.source = b ≫ G.target) (w' : c ≫ G.source = d ≫ G.target),
      a ≫ r = c ≫ r → b ≫ r = d ≫ r → G.compose a b w ≫ r = G.compose c d w' ≫ r) :
    Nonempty (DescendedOperations G q r s t) := by
  have : EffectiveEpi q := hq.effectiveEpi
  have hr : SingletonCover J r := by
    obtain ⟨W, p, f, hp', hf⟩ := exists_local_arrow hp hq (𝟙 A)
    exact SingletonCover.of_comp f r (by simpa [hf] using hp')
  have : EffectiveEpi r := hr.effectiveEpi
  let m : pullback G.source G.target ⟶ pullback s t :=
    pullback.map G.source G.target s t r r q (comp_source_eq_of_isPullback hp).symm
      (comp_target_eq_of_isPullback hp).symm
  have hm : SingletonCover J m := by
    obtain ⟨W, p, f, g, hp', hfg, hf, hg⟩ :=
      exists_local_pair hp hq (pullback.fst s t) (pullback.snd s t) pullback.condition
    let z := pullback.lift f g hfg
    have hz : z ≫ m = p := by
      apply pullback.hom_ext <;> simp [z, m, pullback.map, hf, hg]
    exact SingletonCover.of_comp z m (by simpa [hz] using hp')
  have : EffectiveEpi m := hm.effectiveEpi
  have hc : ∀ {T : Over S} (a b : T ⟶ pullback G.source G.target), a ≫ m = b ≫ m →
      a ≫ G.comp ≫ r = b ≫ G.comp ≫ r := by
    intro T a b hab
    have h₁ : (a ≫ pullback.fst _ _) ≫ r = (b ≫ pullback.fst _ _) ≫ r := by
      simpa [m, pullback.map] using congrArg (· ≫ pullback.fst s t) hab
    have h₂ : (a ≫ pullback.snd _ _) ≫ r = (b ≫ pullback.snd _ _) ≫ r := by
      simpa [m, pullback.map] using congrArg (· ≫ pullback.snd s t) hab
    have ha : (a ≫ pullback.fst _ _) ≫ G.source = (a ≫ pullback.snd _ _) ≫ G.target := by
      simp [Category.assoc, pullback.condition]
    have hb : (b ≫ pullback.fst _ _) ≫ G.source = (b ≫ pullback.snd _ _) ≫ G.target := by
      simp [Category.assoc, pullback.condition]
    have he₁ : pullback.lift (a ≫ pullback.fst _ _) (a ≫ pullback.snd _ _) ha = a := by
      apply pullback.hom_ext <;> simp
    have he₂ : pullback.lift (b ≫ pullback.fst _ _) (b ≫ pullback.snd _ _) hb = b := by
      apply pullback.hom_ext <;> simp
    simpa [GroupoidScheme.compose, he₁, he₂, Category.assoc] using
      hcomp _ _ _ _ ha hb h₁ h₂
  let c := EffectiveEpi.desc m (G.comp ≫ r) hc
  have hc' : m ≫ c = G.comp ≫ r := EffectiveEpi.fac _ _ _
  refine ⟨{ identity := EffectiveEpi.desc q (G.identity ≫ r) hident
            inverse := EffectiveEpi.desc r (G.inverse ≫ r) hinv
            comp := c
            identity_map := EffectiveEpi.fac _ _ _
            inverse_map := EffectiveEpi.fac _ _ _
            comp_map := ?_ }⟩
  intro T f g w w'
  have h : pullback.lift f g w ≫ m = pullback.lift (f ≫ r) (g ≫ r) w' := by
    apply pullback.hom_ext <;> simp [m, pullback.map]
  dsimp only [GroupoidScheme.compose]
  rw [Category.assoc, ← hc', ← Category.assoc, h]

/-- Precomposing `pullback.lift a b w ≫ c` with `p` gives
`pullback.lift (p ≫ a) (p ≫ b) w' ≫ c`. -/
lemma pullback_comp_precomp {C : Type*} [Category C] [HasPullbacks C]
    {Q A T T' : C} {s t : A ⟶ Q} (c : pullback s t ⟶ A)
    (p : T' ⟶ T) (a b : T ⟶ A) (w : a ≫ s = b ≫ t) (w') :
    p ≫ pullback.lift a b w ≫ c = pullback.lift (p ≫ a) (p ≫ b) w' ≫ c := by
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

/-- If arrows `f, g : W ⟶ R` lift `p ≫ a` and `p ≫ b`, then the descended composite of `a` and
`b`, precomposed with `p`, is the image in `A` of the composite of `f` and `g`. -/
lemma DescendedOperations.local_comp {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t) {T W : Over S} (p : W ⟶ T)
    (a b : T ⟶ A) (f g : W ⟶ G.arrows) (w : a ≫ s = b ≫ t)
    (w' : f ≫ G.source = g ≫ G.target) (hf : f ≫ r = p ≫ a) (hg : g ≫ r = p ≫ b) :
    p ≫ pullback.lift a b w ≫ D.comp = G.compose f g w' ≫ r := by
  have hw : (p ≫ a) ≫ s = (p ≫ b) ≫ t := by
    simpa only [Category.assoc] using congrArg (p ≫ ·) w
  rw [pullback_comp_precomp D.comp p a b w hw]
  simpa only [hf, hg] using (D.comp_map f g w' (by rwa [hf, hg])).symm

/-- Given the cartesian square of arrow schemes, if `q` is a singleton cover then so is `r`. -/
lemma arrow_singletonCover {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} (hq : SingletonCover J q) : SingletonCover J r := by
  obtain ⟨W, p, f, hp', hf⟩ := exists_local_arrow hp hq (𝟙 A)
  exact SingletonCover.of_comp f r (by simpa [hf] using hp')

/-- The descended identity, inverse and composition are compatible with `s` and `t`: the
identity is a section of both, the inverse exchanges them, and the composite of `(a, b)` has the
source of `b` and the target of `a`. -/
lemma DescendedOperations.structure_maps {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q) :
    D.identity ≫ s = 𝟙 Q ∧ D.identity ≫ t = 𝟙 Q ∧
      D.inverse ≫ s = t ∧ D.inverse ≫ t = s ∧
      D.comp ≫ s = pullback.snd s t ≫ s ∧ D.comp ≫ t = pullback.fst s t ≫ t := by
  have hs := comp_source_eq_of_isPullback hp
  have ht := comp_target_eq_of_isPullback hp
  have : EffectiveEpi q := hq.effectiveEpi
  have : EffectiveEpi r := (arrow_singletonCover hp hq).effectiveEpi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (cancel_epi q).mp
    simp only [reassoc_of% D.identity_map, hs, reassoc_of% G.source_identity, Category.comp_id]
  · apply (cancel_epi q).mp
    simp only [reassoc_of% D.identity_map, ht, reassoc_of% G.target_identity, Category.comp_id]
  · apply (cancel_epi r).mp
    simp only [reassoc_of% D.inverse_map, hs, ht, reassoc_of% G.source_inverse]
  · apply (cancel_epi r).mp
    simp only [reassoc_of% D.inverse_map, hs, ht, reassoc_of% G.target_inverse]
  all_goals
    obtain ⟨W, p, f, g, hp', w, hf, hg⟩ := exists_local_pair hp hq
      (pullback.fst s t) (pullback.snd s t) pullback.condition
    have : EffectiveEpi p := hp'.effectiveEpi
    have hc : p ≫ D.comp = G.compose f g w ≫ r := by
      simpa only [pullback.lift_fst_snd, Category.id_comp] using
        D.local_comp p _ _ f g pullback.condition w hf hg
    apply (cancel_epi p).mp
  · calc
      p ≫ D.comp ≫ s = G.compose f g w ≫ r ≫ s := by rw [reassoc_of% hc]
      _ = g ≫ r ≫ s := by
        simp [GroupoidScheme.compose, Category.assoc, hs, reassoc_of% G.source_comp]
      _ = p ≫ pullback.snd s t ≫ s := by rw [reassoc_of% hg]
  · calc
      p ≫ D.comp ≫ t = G.compose f g w ≫ r ≫ t := by rw [reassoc_of% hc]
      _ = f ≫ r ≫ t := by
        simp [GroupoidScheme.compose, Category.assoc, ht, reassoc_of% G.target_comp]
      _ = p ≫ pullback.fst s t ≫ t := by rw [reassoc_of% hf]

/-- To prove two morphisms out of `T` equal, one may lift `a : T ⟶ A` to `R` locally on `T`. -/
private lemma eq_of_local_arrow {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q)
    {T X : Over S} (a : T ⟶ A) (u v : T ⟶ X)
    (h : ∀ {W : Over S} (p : W ⟶ T) (f : W ⟶ G.arrows), f ≫ r = p ≫ a → p ≫ u = p ≫ v) :
    u = v := by
  obtain ⟨W, p, f, hp', hf⟩ := exists_local_arrow hp hq a
  have : EffectiveEpi p := hp'.effectiveEpi
  exact (cancel_epi p).mp (h p f hf)

/-- The image in `A` of the identity at the source of a lift `f` of `p ≫ a` is `p ≫ a ≫ s ≫ 𝟙`,
with `𝟙` the descended identity. -/
private lemma DescendedOperations.source_identity_comp {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {T W : Over S} (p : W ⟶ T) (a : T ⟶ A) (f : W ⟶ G.arrows) (hf : f ≫ r = p ≫ a) :
    (f ≫ G.source ≫ G.identity) ≫ r = p ≫ a ≫ s ≫ D.identity := by
  simp only [Category.assoc, ← D.identity_map,
    ← reassoc_of% (comp_source_eq_of_isPullback hp), ← reassoc_of% hf]

/-- The image in `A` of the identity at the target of a lift `f` of `p ≫ a` is `p ≫ a ≫ t ≫ 𝟙`,
with `𝟙` the descended identity. -/
private lemma DescendedOperations.target_identity_comp {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {T W : Over S} (p : W ⟶ T) (a : T ⟶ A) (f : W ⟶ G.arrows) (hf : f ≫ r = p ≫ a) :
    (f ≫ G.target ≫ G.identity) ≫ r = p ≫ a ≫ t ≫ D.identity := by
  simp only [Category.assoc, ← D.identity_map,
    ← reassoc_of% (comp_target_eq_of_isPullback hp), ← reassoc_of% hf]

/-- The descended composition has the descended identities as left units. -/
private lemma DescendedOperations.left_identity {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q)
    {T : Over S} (a : T ⟶ A) (w : (a ≫ t ≫ D.identity) ≫ s = a ≫ t) :
    pullback.lift (a ≫ t ≫ D.identity) a w ≫ D.comp = a := by
  refine eq_of_local_arrow hp hq a _ _ fun p f hf => ?_
  have wf : (f ≫ G.target ≫ G.identity) ≫ G.source = f ≫ G.target := by
    simp [Category.assoc, G.source_identity]
  rw [D.local_comp p _ a (f ≫ G.target ≫ G.identity) f w wf
    (D.target_identity_comp hp p a f hf) hf]
  simpa only [GroupoidScheme.compose, G.left_identity] using hf

/-- The descended composition has the descended identities as right units. -/
private lemma DescendedOperations.right_identity {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q)
    {T : Over S} (a : T ⟶ A) (w : a ≫ s = (a ≫ s ≫ D.identity) ≫ t) :
    pullback.lift a (a ≫ s ≫ D.identity) w ≫ D.comp = a := by
  refine eq_of_local_arrow hp hq a _ _ fun p f hf => ?_
  have wf : f ≫ G.source = (f ≫ G.source ≫ G.identity) ≫ G.target := by
    simp [Category.assoc, G.target_identity]
  rw [D.local_comp p a _ f (f ≫ G.source ≫ G.identity) w wf hf
    (D.source_identity_comp hp p a f hf)]
  simpa only [GroupoidScheme.compose, G.right_identity] using hf

/-- The image in `A` of the inverse of a lift `f` of `p ≫ a` is `p ≫ a ≫ 𝑖`, with `𝑖` the
descended inverse. -/
private lemma DescendedOperations.inverse_comp {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t) {T W : Over S} (p : W ⟶ T) (a : T ⟶ A)
    (f : W ⟶ G.arrows) (hf : f ≫ r = p ≫ a) :
    (f ≫ G.inverse) ≫ r = p ≫ a ≫ D.inverse := by
  rw [Category.assoc, ← D.inverse_map, reassoc_of% hf]

/-- The descended inverse is a left inverse for the descended composition. -/
private lemma DescendedOperations.left_inverse {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q)
    {T : Over S} (a : T ⟶ A) (w : (a ≫ D.inverse) ≫ s = a ≫ t) :
    pullback.lift (a ≫ D.inverse) a w ≫ D.comp = a ≫ s ≫ D.identity := by
  refine eq_of_local_arrow hp hq a _ _ fun p f hf => ?_
  have wf : (f ≫ G.inverse) ≫ G.source = f ≫ G.target := by
    simp [Category.assoc, G.source_inverse]
  rw [D.local_comp p _ a (f ≫ G.inverse) f w wf (D.inverse_comp p a f hf) hf]
  simpa only [GroupoidScheme.compose, G.left_inverse, Category.assoc] using
    D.source_identity_comp hp p a f hf

/-- The descended inverse is a right inverse for the descended composition. -/
private lemma DescendedOperations.right_inverse {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q)
    {T : Over S} (a : T ⟶ A) (w : a ≫ s = (a ≫ D.inverse) ≫ t) :
    pullback.lift a (a ≫ D.inverse) w ≫ D.comp = a ≫ t ≫ D.identity := by
  refine eq_of_local_arrow hp hq a _ _ fun p f hf => ?_
  have wf : f ≫ G.source = (f ≫ G.inverse) ≫ G.target := by
    simp [Category.assoc, G.target_inverse]
  rw [D.local_comp p a _ f (f ≫ G.inverse) w wf hf (D.inverse_comp p a f hf)]
  simpa only [GroupoidScheme.compose, G.right_inverse, Category.assoc] using
    D.target_identity_comp hp p a f hf

/-- The descended composition is associative. -/
private lemma DescendedOperations.assoc {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q)
    {T : Over S} (a b c : T ⟶ A) (wab : a ≫ s = b ≫ t) (wbc : b ≫ s = c ≫ t)
    (w₁ : (pullback.lift a b wab ≫ D.comp) ≫ s = c ≫ t)
    (w₂ : a ≫ s = (pullback.lift b c wbc ≫ D.comp) ≫ t) :
    pullback.lift (pullback.lift a b wab ≫ D.comp) c w₁ ≫ D.comp =
      pullback.lift a (pullback.lift b c wbc ≫ D.comp) w₂ ≫ D.comp := by
  obtain ⟨W, p, f, g, h, hp', wfg, wgh, hf, hg, hh⟩ := exists_local_triple hp hq a b c wab wbc
  have : EffectiveEpi p := hp'.effectiveEpi
  have wfgh : G.compose f g wfg ≫ G.source = h ≫ G.target := by
    simpa [GroupoidScheme.compose, Category.assoc, G.source_comp] using wgh
  have wfgh' : f ≫ G.source = G.compose g h wgh ≫ G.target := by
    simpa [GroupoidScheme.compose, Category.assoc, G.target_comp] using wfg
  apply (cancel_epi p).mp
  rw [D.local_comp p _ c (G.compose f g wfg) h w₁ wfgh
      (D.local_comp p a b f g wab wfg hf hg).symm hh,
    D.local_comp p a _ f (G.compose g h wgh) w₂ wfgh' hf
      (D.local_comp p b c g h wbc wgh hg hh).symm]
  exact congrArg (· ≫ r) (G.assoc W f g h wfg wgh wfgh wfgh')

/-- The descended structure morphisms make `(Q, A, s, t)` into a groupoid scheme `K` with a
morphism `G ⟶ K` given by `q` and `r`, whose square of arrow schemes over the pairs of objects is
cartesian and which is fully faithful on `T`-valued points for every `T`. -/
lemma DescendedOperations.exists_groupoid {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q) :
    ∃ (K : GroupoidScheme S) (he : K.objects = Q) (F : GroupoidScheme.Hom G K),
      F.mapObjects = q ≫ eqToHom he.symm ∧
        IsPullback F.mapArrows (prod.lift G.target G.source) (prod.lift K.target K.source)
          (prod.map F.mapObjects F.mapObjects) ∧
        ∀ T : Over S, Nonempty (F.evaluation T).FullyFaithful := by
  obtain ⟨hids, hidt, hinvs, hinvt, hcs, hct⟩ := D.structure_maps hp hq
  let K : GroupoidScheme S :=
    { objects := Q, arrows := A, source := s, target := t,
      comp := D.comp, identity := D.identity, inverse := D.inverse,
      source_identity := hids, target_identity := hidt,
      source_inverse := hinvs, target_inverse := hinvt,
      source_comp := hcs, target_comp := hct,
      left_identity := fun _ a w ↦ D.left_identity hp hq a w,
      right_identity := fun _ a w ↦ D.right_identity hp hq a w,
      left_inverse := fun _ a w ↦ D.left_inverse hp hq a w,
      right_inverse := fun _ a w ↦ D.right_inverse hp hq a w,
      assoc := fun _ a b c wab wbc w₁ w₂ ↦ D.assoc hp hq a b c wab wbc w₁ w₂ }
  let F : GroupoidScheme.Hom G K :=
    { mapObjects := q, mapArrows := r, map_source := comp_source_eq_of_isPullback hp,
      map_target := comp_target_eq_of_isPullback hp,
      map_identity := D.identity_map, map_comp := fun _ ↦ D.comp_map }
  exact ⟨K, rfl, F, by simp [F], hp, evaluation_fullyFaithful_of_isPullback F hp⟩

end AlgebraicGeometry

end
