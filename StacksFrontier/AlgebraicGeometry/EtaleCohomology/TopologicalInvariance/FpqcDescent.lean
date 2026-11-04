module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcEffectivity
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityBaseLocal
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent

/-!
# Descending an étale scheme through an affine étale covering of the target

Let `f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y` be étale, surjective and
quasi-compact, and let `p : U ⟶ X` be a morphism of schemes. Suppose that the base change of `U`
to `W ×_Y X` is the base change of a scheme `t : T ⟶ W` which is étale and affine over `W`, that
is that `T ×_Y X` and `U ×_Y W` are identified over `X` and over `W`. Then `U` is, over `X`, the
base change along `f` of a scheme étale over `Y`.

This is the third step of the second proof of Stacks Project, Tag 04DZ, where it discharges the
descent that the induction on a bound for the fibre degrees of an étale morphism of affine
schemes performs at each step.

## The argument

Base change along a universal homeomorphism is full and faithful on schemes étale over the
target, by Stacks Project, Tag 0BTY, in the elementary form
`Stacks.Etale.existsUnique_hom_of_pullback_hom`. This is used three times.

*The gluing isomorphism.* The scheme `U` carries the canonical descent datum relative to
`W ×_Y X ⟶ X`, which is an fpqc covering because `w` is. Read through the identification of
`U ×_Y W` with `T ×_Y X`, its gluing isomorphism is an isomorphism between the two base changes
of `T ×_Y X` to `W ×_Y W ×_Y X`, that is between the base changes along `f` of the two étale
`Y`-schemes `T ×_Y W` and `W ×_Y T`. Full faithfulness produces from it a unique isomorphism
`T ×_Y W ≅ W ×_Y T` over `W ×_Y W`, which is the gluing isomorphism of a descent datum relative
to `w`.

*The cocycle condition.* Both sides of the condition are morphisms of étale `Y`-schemes, so
faithfulness reduces the condition to its base change along `f`, where it is a computation with
the identification.

*Effectivity and the comparison.* The structure morphism `T ⟶ W` is affine, so Stacks Project,
Tag 0245 — here `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom` — makes the datum
effective: there is a scheme `V ⟶ Y` whose base change along `w` is `T`, compatibly with the
gluing isomorphism. It is étale because being étale descends along an fpqc covering. Finally
`V ×_Y X` and `U` have identified base changes to `W ×_Y X`, compatibly with the canonical
descent data, so they are identified over `X` by descent of morphisms along an fpqc covering,
Stacks Project, Tag 040L.

## Main definitions

* `Stacks.Etale.uCoordOfPullbackIso` and `Stacks.Etale.tCoord` — the identification of
  `T ×_Y X` with `U ×_Y W`, read on generalized points in the two directions.
* `Stacks.Etale.shift` — the action by which the gluing isomorphism of the descent datum
  operates: a point of `T` is moved onto a prescribed point of `W`, keeping its `U`-coordinate.
* `Stacks.Etale.srcHom` and `Stacks.Etale.tgtHom` — the structure morphisms of `T ×_Y W` and
  `W ×_Y T` over `Y`, between which the gluing isomorphism goes.

## Main results

* `Stacks.Etale.eq_of_pullbackFst_comp_eq_of_etale` — faithfulness of base change along a
  universal homeomorphism, read on the projections of the fibre products: two morphisms of
  `Y`-schemes into a scheme étale over `Y` whose base changes along `f` agree are equal.
* `Stacks.Etale.shift_shift` — shifting twice is shifting once, which is the cocycle condition.
* `Stacks.Etale.shift_eq_actPullback` — the shift is the action of the descended gluing
  isomorphism, so in particular it does not depend on the point of `X` through which it is
  computed.
* `Stacks.Etale.d_hom_comp_fst` and `Stacks.Etale.d_hom_comp_snd` — the descended gluing
  isomorphism lies over `W ×_Y W`.
* `Stacks.Etale.actPullbackLaw_gluing` — the cocycle condition for it.
* `Stacks.Etale.exists_etale_pullback_iso_of_etaleCoverComparison` — the statement above.

## Implementation notes

Everything is phrased through the two projections of literal fibre products rather than in the
over-category, which is the convention of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence`. The
identification of `T ×_Y X` with `U ×_Y W` is used only through the two "coordinate" operations
`Stacks.Etale.uCoordOfPullbackIso` and `Stacks.Etale.tCoord`, which read it on generalized
points: a point of `T` and a point of `X` over one point of `Y` determine a point of `U`, and a
point of `U` and a point of `W` over one point of `Y` determine a point of `T`. Every diagram of
the argument becomes an identity between composites of these two operations.

The descent datum is built by `AlgebraicGeometry.DescentDatum.ofPullbackIso`, whose cocycle
condition is the law that acting twice is acting once, and reduced to the universal triple by
`AlgebraicGeometry.DescentDatum.actPullbackLaw_of_universal`. The descended scheme is extracted
as a `AlgebraicGeometry.DescentData.Chart`, which carries both the cartesian square exhibiting
`T` as a base change and the compatibility of the gluing isomorphism with the projection; the
latter is what the comparison at the end consumes.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 040L](https://stacks.math.columbia.edu/tag/040L)
* [Stacks Project, Tag 02VN](https://stacks.math.columbia.edu/tag/02VN)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Faithfulness of base change in elementary form -/

/-- **Base change along a universal homeomorphism is faithful, read on the fibre products.** Let
`f : X ⟶ Y` be a universal homeomorphism, let `q : Z ⟶ Y` be arbitrary and let `r : V ⟶ Y` be
étale. Two morphisms `Z ⟶ V` over `Y` which agree after restriction along the projection
`Z ×_Y X ⟶ Z` are equal.

This is the uniqueness half of Stacks Project, Tag 0BTY; the projection `Z ×_Y X ⟶ Z` is a base
change of `f`, which is not flat, so the statement is not an instance of the epimorphy of a
faithfully flat morphism. -/
theorem eq_of_pullbackFst_comp_eq_of_etale (f : X ⟶ Y) [UniversalHomeomorphism f]
    {Z V : Scheme.{u}} (q : Z ⟶ Y) (r : V ⟶ Y) [Etale r] {α β : Z ⟶ V}
    (hα : α ≫ r = q) (hβ : β ≫ r = q)
    (h : pullback.fst q f ≫ α = pullback.fst q f ≫ β) : α = β := by
  have hc : (pullback.fst q f ≫ α) ≫ r = pullback.snd q f ≫ f := by
    rw [Category.assoc, hα]
    exact pullback.condition
  obtain ⟨ψ, -, huniq⟩ := existsUnique_hom_of_pullback_hom f q r
    (pullback.lift (pullback.fst q f ≫ α) (pullback.snd q f) hc) (pullback.lift_snd _ _ _)
  rw [huniq α ⟨hα, (pullback.lift_fst _ _ _).symm⟩,
    huniq β ⟨hβ, by rw [pullback.lift_fst]; exact h.symm⟩]

/-! ### Reading an identification of two fibre products on generalized points -/

/-- Precomposing a morphism into a fibre product with a morphism of test schemes. -/
private lemma comp_pullback_lift {A B C Z Z' : Scheme.{u}} (a : A ⟶ C) (b : B ⟶ C)
    (k : Z' ⟶ Z) (x : Z ⟶ A) (y : Z ⟶ B) (hxy : x ≫ a = y ≫ b)
    (hxy' : (k ≫ x) ≫ a = (k ≫ y) ≫ b) :
    k ≫ pullback.lift x y hxy = pullback.lift (k ≫ x) (k ≫ y) hxy' := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

section Coord

variable (f : X ⟶ Y) {W T U : Scheme.{u}} (w : W ⟶ Y) (t : T ⟶ W) (p : U ⟶ X)
  (ε : pullback (t ≫ w) f ≅ pullback (p ≫ f) w)

/-- **The `U`-coordinate of a point of `T` and a point of `X`.** Given an identification `ε` of
`T ×_Y X` with `U ×_Y W`, a point of `T` and a point of `X` lying over one point of `Y` determine
a point of `U`. -/
def uCoordOfPullbackIso {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (h : τ ≫ t ≫ w = x ≫ f) : Z ⟶ U :=
  pullback.lift τ x h ≫ ε.hom ≫ pullback.fst (p ≫ f) w

/-- **The `T`-coordinate of a point of `U` and a point of `W`.** Given an identification `ε` of
`T ×_Y X` with `U ×_Y W`, a point of `U` and a point of `W` lying over one point of `Y` determine
a point of `T`. -/
def tCoord {Z : Scheme.{u}} (u : Z ⟶ U) (ω : Z ⟶ W) (h : u ≫ p ≫ f = ω ≫ w) : Z ⟶ T :=
  pullback.lift u ω h ≫ ε.inv ≫ pullback.fst (t ≫ w) f

/-- The `U`-coordinate depends only on the two points, not on the proof that they lie over one
point of `Y`. -/
lemma uCoordOfPullbackIso_congr {Z : Scheme.{u}} {τ τ' : Z ⟶ T} {x x' : Z ⟶ X} (hτ : τ = τ')
    (hx : x = x')
    (h : τ ≫ t ≫ w = x ≫ f) (h' : τ' ≫ t ≫ w = x' ≫ f) :
    uCoordOfPullbackIso f w t p ε τ x h = uCoordOfPullbackIso f w t p ε τ' x' h' := by
  subst hτ; subst hx; rfl

/-- The `T`-coordinate depends only on the two points, not on the proof that they lie over one
point of `Y`. -/
lemma tCoord_congr {Z : Scheme.{u}} {u u' : Z ⟶ U} {ω ω' : Z ⟶ W} (hu : u = u') (hω : ω = ω')
    (h : u ≫ p ≫ f = ω ≫ w) (h' : u' ≫ p ≫ f = ω' ≫ w) :
    tCoord f w t p ε u ω h = tCoord f w t p ε u' ω' h' := by
  subst hu; subst hω; rfl

variable (h1 : ε.hom ≫ pullback.fst (p ≫ f) w ≫ p = pullback.snd (t ≫ w) f)
  (h2 : ε.hom ≫ pullback.snd (p ≫ f) w = pullback.fst (t ≫ w) f ≫ t)

include h1 in
/-- Under `ε⁻¹`, the projection of `T ×_Y X` to `X` is the projection of `U ×_Y W` to `U`
followed by `p`. -/
lemma inv_comp_snd :
    ε.inv ≫ pullback.snd (t ≫ w) f = pullback.fst (p ≫ f) w ≫ p := by
  rw [← h1, ← Category.assoc, ε.inv_hom_id, Category.id_comp]

include h2 in
/-- Under `ε⁻¹`, the projection of `T ×_Y X` to `T` followed by `t` is the projection of
`U ×_Y W` to `W`. -/
lemma inv_comp_fst_comp :
    ε.inv ≫ pullback.fst (t ≫ w) f ≫ t = pullback.snd (p ≫ f) w := by
  rw [← h2, ← Category.assoc, ε.inv_hom_id, Category.id_comp]

include h1 in
/-- The `U`-coordinate lies over the given point of `X`. -/
lemma uCoordOfPullbackIso_comp {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (h : τ ≫ t ≫ w = x ≫ f) :
    uCoordOfPullbackIso f w t p ε τ x h ≫ p = x := by
  calc uCoordOfPullbackIso f w t p ε τ x h ≫ p
      = pullback.lift τ x h ≫ ε.hom ≫ pullback.fst (p ≫ f) w ≫ p := by
        simp only [uCoordOfPullbackIso, Category.assoc]
    _ = pullback.lift τ x h ≫ pullback.snd (t ≫ w) f := by rw [h1]
    _ = x := pullback.lift_snd _ _ _

include h2 in
/-- The `T`-coordinate lies over the given point of `W`. -/
lemma tCoord_comp {Z : Scheme.{u}} (u : Z ⟶ U) (ω : Z ⟶ W) (h : u ≫ p ≫ f = ω ≫ w) :
    tCoord f w t p ε u ω h ≫ t = ω := by
  calc tCoord f w t p ε u ω h ≫ t
      = pullback.lift u ω h ≫ ε.inv ≫ pullback.fst (t ≫ w) f ≫ t := by
        simp only [tCoord, Category.assoc]
    _ = pullback.lift u ω h ≫ pullback.snd (p ≫ f) w := by rw [inv_comp_fst_comp f w t p ε h2]
    _ = ω := pullback.lift_snd _ _ _

include h2 in
/-- The identification carries the pair of a point of `T` and a point of `X` to the pair of its
`U`-coordinate and the image in `W` of the point of `T`. -/
lemma lift_comp_hom {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (h : τ ≫ t ≫ w = x ≫ f)
    (h' : uCoordOfPullbackIso f w t p ε τ x h ≫ p ≫ f = (τ ≫ t) ≫ w) :
    pullback.lift τ x h ≫ ε.hom =
      pullback.lift (uCoordOfPullbackIso f w t p ε τ x h) (τ ≫ t) h' := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, Category.assoc]
    rfl
  · rw [pullback.lift_snd, Category.assoc, h2, ← Category.assoc, pullback.lift_fst]

include h1 in
/-- The inverse identification carries the pair of a point of `U` and a point of `W` to the pair
of its `T`-coordinate and the image in `X` of the point of `U`. -/
lemma lift_comp_inv {Z : Scheme.{u}} (u : Z ⟶ U) (ω : Z ⟶ W) (h : u ≫ p ≫ f = ω ≫ w)
    (h' : tCoord f w t p ε u ω h ≫ t ≫ w = (u ≫ p) ≫ f) :
    pullback.lift u ω h ≫ ε.inv = pullback.lift (tCoord f w t p ε u ω h) (u ≫ p) h' := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, Category.assoc]
    rfl
  · rw [pullback.lift_snd, Category.assoc, inv_comp_snd f w t p ε h1, ← Category.assoc,
      pullback.lift_fst]

include h2 in
/-- Taking the `T`-coordinate of a `U`-coordinate returns the point of `T` one started from. -/
lemma tCoord_uCoordOfPullbackIso {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (h : τ ≫ t ≫ w = x ≫ f)
    (h' : uCoordOfPullbackIso f w t p ε τ x h ≫ p ≫ f = (τ ≫ t) ≫ w) :
    tCoord f w t p ε (uCoordOfPullbackIso f w t p ε τ x h) (τ ≫ t) h' = τ := by
  calc tCoord f w t p ε (uCoordOfPullbackIso f w t p ε τ x h) (τ ≫ t) h'
      = (pullback.lift τ x h ≫ ε.hom) ≫ ε.inv ≫ pullback.fst (t ≫ w) f := by
        rw [tCoord, lift_comp_hom f w t p ε h2 τ x h h']
    _ = pullback.lift τ x h ≫ pullback.fst (t ≫ w) f := by
        rw [Category.assoc, ← Category.assoc ε.hom, ε.hom_inv_id, Category.id_comp]
    _ = τ := pullback.lift_fst _ _ _

include h1 in
/-- Taking the `U`-coordinate of a `T`-coordinate returns the point of `U` one started from. -/
lemma uCoordOfPullbackIso_tCoord {Z : Scheme.{u}} (u : Z ⟶ U) (ω : Z ⟶ W) (h : u ≫ p ≫ f = ω ≫ w)
    (h' : tCoord f w t p ε u ω h ≫ t ≫ w = (u ≫ p) ≫ f) :
    uCoordOfPullbackIso f w t p ε (tCoord f w t p ε u ω h) (u ≫ p) h' = u := by
  calc uCoordOfPullbackIso f w t p ε (tCoord f w t p ε u ω h) (u ≫ p) h'
      = (pullback.lift u ω h ≫ ε.inv) ≫ ε.hom ≫ pullback.fst (p ≫ f) w := by
        rw [uCoordOfPullbackIso, lift_comp_inv f w t p ε h1 u ω h h']
    _ = pullback.lift u ω h ≫ pullback.fst (p ≫ f) w := by
        rw [Category.assoc, ← Category.assoc ε.inv, ε.inv_hom_id, Category.id_comp]
    _ = u := pullback.lift_fst _ _ _

/-- The `U`-coordinate commutes with change of test scheme. -/
lemma comp_uCoordOfPullbackIso {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (τ : Z ⟶ T) (x : Z ⟶ X)
    (h : τ ≫ t ≫ w = x ≫ f) (h' : (k ≫ τ) ≫ t ≫ w = (k ≫ x) ≫ f) :
    k ≫ uCoordOfPullbackIso f w t p ε τ x h = uCoordOfPullbackIso f w t p ε (k ≫ τ) (k ≫ x) h' := by
  rw [uCoordOfPullbackIso, uCoordOfPullbackIso, ← Category.assoc,
    comp_pullback_lift (t ≫ w) f k τ x h h']

/-- The `T`-coordinate commutes with change of test scheme. -/
lemma comp_tCoord {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (u : Z ⟶ U) (ω : Z ⟶ W)
    (h : u ≫ p ≫ f = ω ≫ w) (h' : (k ≫ u) ≫ p ≫ f = (k ≫ ω) ≫ w) :
    k ≫ tCoord f w t p ε u ω h = tCoord f w t p ε (k ≫ u) (k ≫ ω) h' := by
  rw [tCoord, tCoord, ← Category.assoc, comp_pullback_lift (p ≫ f) w k u ω h h']

/-! ### The action by which the gluing isomorphism operates -/

include h1 in
/-- **Moving a point of `T` to a prescribed point of `W`.** Let `τ` be a point of `T` and `x` a
point of `X` over one point of `Y`, and let `ω` be a further point of `W` over that same point of
`Y`. This is the point of `T` lying over `ω` whose `U`-coordinate at `x` is that of `τ`.

This is the action by which the gluing isomorphism of the descent datum of `T` operates, and the
cocycle condition is the statement `Stacks.Etale.shift_shift` that acting twice is acting
once. -/
def shift {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (ω : Z ⟶ W)
    (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f) : Z ⟶ T :=
  tCoord f w t p ε (uCoordOfPullbackIso f w t p ε τ x hτ) ω
    (by rw [← Category.assoc, uCoordOfPullbackIso_comp f w t p ε h1]; exact hω.symm)

include h1 h2 in
/-- The shifted point lies over the prescribed point of `W`. -/
lemma shift_comp_t {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (ω : Z ⟶ W)
    (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f) :
    shift f w t p ε h1 τ x ω hτ hω ≫ t = ω :=
  tCoord_comp f w t p ε h2 _ _ _

include h1 h2 in
/-- The shifted point lies over the same point of `Y` as the point of `X`. -/
lemma shift_comp {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (ω : Z ⟶ W)
    (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f) :
    shift f w t p ε h1 τ x ω hτ hω ≫ t ≫ w = x ≫ f := by
  rw [← Category.assoc, shift_comp_t f w t p ε h1 h2]
  exact hω

include h1 in
/-- Shifting leaves the `U`-coordinate unchanged. -/
lemma uCoordOfPullbackIso_shift {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (ω : Z ⟶ W)
    (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f)
    (h' : shift f w t p ε h1 τ x ω hτ hω ≫ t ≫ w = x ≫ f) :
    uCoordOfPullbackIso f w t p ε (shift f w t p ε h1 τ x ω hτ hω) x h' =
      uCoordOfPullbackIso f w t p ε τ x hτ := by
  have hu : uCoordOfPullbackIso f w t p ε τ x hτ ≫ p = x :=
    uCoordOfPullbackIso_comp f w t p ε h1 τ x hτ
  have h'' : shift f w t p ε h1 τ x ω hτ hω ≫ t ≫ w
      = (uCoordOfPullbackIso f w t p ε τ x hτ ≫ p) ≫ f := by rw [hu]; exact h'
  exact (uCoordOfPullbackIso_congr f w t p ε rfl hu.symm h' h'').trans
    (uCoordOfPullbackIso_tCoord f w t p ε h1 _ _ _ h'')

include h1 h2 in
/-- **Acting twice is acting once.** This is the cocycle condition for the gluing isomorphism of
the descent datum of `T`. -/
lemma shift_shift {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (ω ω' : Z ⟶ W)
    (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f) (hω' : ω' ≫ w = x ≫ f)
    (h' : shift f w t p ε h1 τ x ω hτ hω ≫ t ≫ w = x ≫ f) :
    shift f w t p ε h1 (shift f w t p ε h1 τ x ω hτ hω) x ω' h' hω'
      = shift f w t p ε h1 τ x ω' hτ hω' :=
  tCoord_congr f w t p ε (uCoordOfPullbackIso_shift f w t p ε h1 τ x ω hτ hω h') rfl _ _

include h1 h2 in
/-- Shifting a point of `T` to the point of `W` it already lies over changes nothing. -/
lemma shift_self {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X)
    (hτ : τ ≫ t ≫ w = x ≫ f) (hω : (τ ≫ t) ≫ w = x ≫ f) :
    shift f w t p ε h1 τ x (τ ≫ t) hτ hω = τ :=
  tCoord_uCoordOfPullbackIso f w t p ε h2 τ x hτ _

include h1 in
/-- The action commutes with change of test scheme. -/
lemma comp_shift {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (τ : Z ⟶ T) (x : Z ⟶ X) (ω : Z ⟶ W)
    (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f)
    (hτ' : (k ≫ τ) ≫ t ≫ w = (k ≫ x) ≫ f) (hω' : (k ≫ ω) ≫ w = (k ≫ x) ≫ f) :
    k ≫ shift f w t p ε h1 τ x ω hτ hω
      = shift f w t p ε h1 (k ≫ τ) (k ≫ x) (k ≫ ω) hτ' hω' := by
  refine Eq.trans (comp_tCoord f w t p ε k _ _ _ ?_) ?_
  · rw [comp_uCoordOfPullbackIso f w t p ε k τ x hτ hτ', ← Category.assoc,
      uCoordOfPullbackIso_comp f w t p ε h1 (k ≫ τ) (k ≫ x) hτ']
    exact hω'.symm
  · exact tCoord_congr f w t p ε (comp_uCoordOfPullbackIso f w t p ε k τ x hτ hτ') rfl _ _

include h1 in
/-- The action depends only on the three points. -/
lemma shift_congr {Z : Scheme.{u}} {τ τ' : Z ⟶ T} {x x' : Z ⟶ X} {ω ω' : Z ⟶ W}
    (hτe : τ = τ') (hxe : x = x') (hωe : ω = ω')
    (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f)
    (hτ2 : τ' ≫ t ≫ w = x' ≫ f) (hω2 : ω' ≫ w = x' ≫ f) :
    shift f w t p ε h1 τ x ω hτ hω = shift f w t p ε h1 τ' x' ω' hτ2 hω2 := by
  subst hτe; subst hxe; subst hωe; rfl

/-! ### The gluing isomorphism of the descent datum, read after base change -/

/-- The structure morphism over `Y` of `T ×_Y W`. -/
def srcHom : pullback (t ≫ w) w ⟶ Y :=
  pullback.fst (t ≫ w) w ≫ t ≫ w

/-- The structure morphism over `Y` of `W ×_Y T`. -/
def tgtHom : pullback w (t ≫ w) ⟶ Y :=
  pullback.fst w (t ≫ w) ≫ w

/-- The point of `T` underlying a point of `(T ×_Y W) ×_Y X`. -/
def srcT : pullback (srcHom w t) f ⟶ T :=
  pullback.fst (srcHom w t) f ≫ pullback.fst (t ≫ w) w

/-- The point of `W` underlying a point of `(T ×_Y W) ×_Y X`. -/
def srcW : pullback (srcHom w t) f ⟶ W :=
  pullback.fst (srcHom w t) f ≫ pullback.snd (t ≫ w) w

/-- The point of `X` underlying a point of `(T ×_Y W) ×_Y X`. -/
def srcX : pullback (srcHom w t) f ⟶ X :=
  pullback.snd (srcHom w t) f

/-- The point of `W` underlying a point of `(W ×_Y T) ×_Y X`. -/
def tgtW : pullback (tgtHom w t) f ⟶ W :=
  pullback.fst (tgtHom w t) f ≫ pullback.fst w (t ≫ w)

/-- The point of `T` underlying a point of `(W ×_Y T) ×_Y X`. -/
def tgtT : pullback (tgtHom w t) f ⟶ T :=
  pullback.fst (tgtHom w t) f ≫ pullback.snd w (t ≫ w)

/-- The point of `X` underlying a point of `(W ×_Y T) ×_Y X`. -/
def tgtX : pullback (tgtHom w t) f ⟶ X :=
  pullback.snd (tgtHom w t) f

/-- The point of `T` and the point of `X` underlying a point of `(T ×_Y W) ×_Y X` lie over one
point of `Y`. -/
lemma srcT_comp : srcT f w t ≫ t ≫ w = srcX f w t ≫ f := by
  rw [srcT, srcX, Category.assoc]
  exact pullback.condition

/-- The structure morphism of `T ×_Y W` over `Y`, read through the second projection. -/
lemma srcHom_eq : srcHom w t = pullback.snd (t ≫ w) w ≫ w :=
  pullback.condition

/-- The point of `W` and the point of `X` underlying a point of `(T ×_Y W) ×_Y X` lie over one
point of `Y`. -/
lemma srcW_comp : srcW f w t ≫ w = srcX f w t ≫ f := by
  calc srcW f w t ≫ w
      = pullback.fst (srcHom w t) f ≫ pullback.snd (t ≫ w) w ≫ w := by
        rw [srcW, Category.assoc]
    _ = pullback.fst (srcHom w t) f ≫ srcHom w t :=
        congrArg (fun m => pullback.fst (srcHom w t) f ≫ m) (srcHom_eq w t).symm
    _ = srcX f w t ≫ f := pullback.condition

/-- The point of `W` and the point of `X` underlying a point of `(W ×_Y T) ×_Y X` lie over one
point of `Y`. -/
lemma tgtW_comp : tgtW f w t ≫ w = tgtX f w t ≫ f := by
  rw [tgtW, tgtX, Category.assoc]
  exact pullback.condition

/-- The structure morphism of `W ×_Y T` over `Y`, read through the second projection. -/
lemma tgtHom_eq : tgtHom w t = pullback.snd w (t ≫ w) ≫ t ≫ w :=
  pullback.condition

/-- The point of `T` and the point of `X` underlying a point of `(W ×_Y T) ×_Y X` lie over one
point of `Y`. -/
lemma tgtT_comp : tgtT f w t ≫ t ≫ w = tgtX f w t ≫ f := by
  calc tgtT f w t ≫ t ≫ w
      = pullback.fst (tgtHom w t) f ≫ pullback.snd w (t ≫ w) ≫ t ≫ w := by
        rw [tgtT, Category.assoc]
    _ = pullback.fst (tgtHom w t) f ≫ tgtHom w t :=
        congrArg (fun m => pullback.fst (tgtHom w t) f ≫ m) (tgtHom_eq w t).symm
    _ = tgtX f w t ≫ f := pullback.condition

include h1 h2 in
/-- **The gluing isomorphism after base change along `f`.** On a point of `(T ×_Y W) ×_Y X` it
keeps the point of `X`, replaces the point of `T` by its image in `W`, and replaces the point of
`W` by the point of `T` shifted onto it. -/
def gluingFwd : pullback (srcHom w t) f ⟶ pullback (tgtHom w t) f :=
  pullback.lift
    (pullback.lift (srcT f w t ≫ t)
      (shift f w t p ε h1 (srcT f w t) (srcX f w t) (srcW f w t) (srcT_comp f w t)
        (srcW_comp f w t))
      (by
        rw [shift_comp f w t p ε h1 h2, Category.assoc]
        exact srcT_comp f w t))
    (srcX f w t)
    (by
      rw [tgtHom, ← Category.assoc, pullback.lift_fst, Category.assoc]
      exact srcT_comp f w t)

include h1 h2 in
/-- **The inverse gluing isomorphism after base change along `f`.** -/
def gluingBwd : pullback (tgtHom w t) f ⟶ pullback (srcHom w t) f :=
  pullback.lift
    (pullback.lift
      (shift f w t p ε h1 (tgtT f w t) (tgtX f w t) (tgtW f w t) (tgtT_comp f w t)
        (tgtW_comp f w t))
      (tgtT f w t ≫ t)
      (by
        rw [shift_comp f w t p ε h1 h2, Category.assoc]
        exact (tgtT_comp f w t).symm))
    (tgtX f w t)
    (by
      rw [srcHom, ← Category.assoc, pullback.lift_fst]
      exact shift_comp f w t p ε h1 h2 _ _ _ _ _)

include h1 h2 in
/-- The gluing isomorphism sends the point of `W` to the image in `W` of the point of `T`. -/
lemma gluingFwd_comp_tgtW : gluingFwd f w t p ε h1 h2 ≫ tgtW f w t = srcT f w t ≫ t := by
  rw [tgtW, gluingFwd, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]

include h1 h2 in
/-- The gluing isomorphism sends the point of `T` to the shifted point. -/
lemma gluingFwd_comp_tgtT :
    gluingFwd f w t p ε h1 h2 ≫ tgtT f w t =
      shift f w t p ε h1 (srcT f w t) (srcX f w t) (srcW f w t) (srcT_comp f w t)
        (srcW_comp f w t) := by
  rw [tgtT, gluingFwd, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]

include h1 h2 in
/-- The gluing isomorphism preserves the point of `X`. -/
lemma gluingFwd_comp_tgtX : gluingFwd f w t p ε h1 h2 ≫ tgtX f w t = srcX f w t := by
  rw [tgtX, gluingFwd, pullback.lift_snd]

include h1 h2 in
/-- The inverse gluing isomorphism sends the point of `T` to the shifted point. -/
lemma gluingBwd_comp_srcT :
    gluingBwd f w t p ε h1 h2 ≫ srcT f w t =
      shift f w t p ε h1 (tgtT f w t) (tgtX f w t) (tgtW f w t) (tgtT_comp f w t)
        (tgtW_comp f w t) := by
  rw [srcT, gluingBwd, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]

include h1 h2 in
/-- The inverse gluing isomorphism sends the point of `W` to the image in `W` of the point of
`T`. -/
lemma gluingBwd_comp_srcW :
    gluingBwd f w t p ε h1 h2 ≫ srcW f w t = tgtT f w t ≫ t := by
  rw [srcW, gluingBwd, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]

include h1 h2 in
/-- The inverse gluing isomorphism preserves the point of `X`. -/
lemma gluingBwd_comp_srcX :
    gluingBwd f w t p ε h1 h2 ≫ srcX f w t = tgtX f w t := by
  rw [srcX, gluingBwd, pullback.lift_snd]

/-- A morphism into `(T ×_Y W) ×_Y X` is determined by its three coordinates. -/
lemma src_hom_ext {Z : Scheme.{u}} {m m' : Z ⟶ pullback (srcHom w t) f}
    (hT : m ≫ srcT f w t = m' ≫ srcT f w t) (hW : m ≫ srcW f w t = m' ≫ srcW f w t)
    (hX : m ≫ srcX f w t = m' ≫ srcX f w t) : m = m' := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) hX
  · rw [Category.assoc, Category.assoc]; exact hT
  · rw [Category.assoc, Category.assoc]; exact hW

/-- A morphism into `(W ×_Y T) ×_Y X` is determined by its three coordinates. -/
lemma tgt_hom_ext {Z : Scheme.{u}} {m m' : Z ⟶ pullback (tgtHom w t) f}
    (hW : m ≫ tgtW f w t = m' ≫ tgtW f w t) (hT : m ≫ tgtT f w t = m' ≫ tgtT f w t)
    (hX : m ≫ tgtX f w t = m' ≫ tgtX f w t) : m = m' := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) hX
  · rw [Category.assoc, Category.assoc]; exact hW
  · rw [Category.assoc, Category.assoc]; exact hT

/-- Precomposing the shift of `τ` with a morphism `m` that carries `τ` to a shifted point `a`
onto the point `a ≫ t` of `W` gives back `a`. -/
private lemma comp_shift_eq_of_shift {Z Z' : Scheme.{u}} (h1 : ε.hom ≫ pullback.fst (p ≫ f) w ≫ p =
      pullback.snd (t ≫ w) f)
    (h2 : ε.hom ≫ pullback.snd (p ≫ f) w = pullback.fst (t ≫ w) f ≫ t) (m : Z' ⟶ Z)
    (τ : Z ⟶ T) (x : Z ⟶ X) (ω : Z ⟶ W) (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f)
    (a : Z' ⟶ T) (b : Z' ⟶ X) (c : Z' ⟶ W) (ha : a ≫ t ≫ w = b ≫ f) (hc : c ≫ w = b ≫ f)
    (hmτ : m ≫ τ = shift f w t p ε h1 a b c ha hc) (hmx : m ≫ x = b) (hmω : m ≫ ω = a ≫ t) :
    m ≫ shift f w t p ε h1 τ x ω hτ hω = a := by
  have hac : (a ≫ t) ≫ w = b ≫ f := (Category.assoc _ _ _).trans ha
  have hs := shift_comp f w t p ε h1 h2 a b c ha hc
  have hτ' : (m ≫ τ) ≫ t ≫ w = (m ≫ x) ≫ f := by rw [hmτ, hmx]; exact hs
  have hω' : (m ≫ ω) ≫ w = (m ≫ x) ≫ f := by rw [hmω, hmx]; exact hac
  rw [comp_shift f w t p ε h1 m τ x ω hτ hω hτ' hω']
  exact (shift_congr f w t p ε h1 hmτ hmx hmω hτ' hω' hs hac).trans
    ((shift_shift f w t p ε h1 h2 a b c _ ha hc hac hs).trans
      (shift_self f w t p ε h1 h2 a b ha hac))

include h1 h2 in
/-- The two morphisms of this section are mutually inverse, one way round. -/
lemma gluingFwd_gluingBwd :
    gluingFwd f w t p ε h1 h2 ≫ gluingBwd f w t p ε h1 h2 = 𝟙 _ := by
  refine src_hom_ext f w t ?_ ?_ ?_
  · rw [Category.assoc, gluingBwd_comp_srcT f w t p ε h1 h2, Category.id_comp]
    exact comp_shift_eq_of_shift f w t p ε h1 h2 _ _ _ _ _ _ _ _ _ _ _
      (gluingFwd_comp_tgtT f w t p ε h1 h2) (gluingFwd_comp_tgtX f w t p ε h1 h2)
      (gluingFwd_comp_tgtW f w t p ε h1 h2)
  · rw [Category.assoc, gluingBwd_comp_srcW f w t p ε h1 h2, ← Category.assoc,
      gluingFwd_comp_tgtT f w t p ε h1 h2, Category.id_comp,
      shift_comp_t f w t p ε h1 h2]
  · rw [Category.assoc, gluingBwd_comp_srcX f w t p ε h1 h2,
      gluingFwd_comp_tgtX f w t p ε h1 h2, Category.id_comp]

include h1 h2 in
/-- The two morphisms of this section are mutually inverse, the other way round. -/
lemma gluingBwd_gluingFwd :
    gluingBwd f w t p ε h1 h2 ≫ gluingFwd f w t p ε h1 h2 = 𝟙 _ := by
  refine tgt_hom_ext f w t ?_ ?_ ?_
  · rw [Category.assoc, gluingFwd_comp_tgtW f w t p ε h1 h2, ← Category.assoc,
      gluingBwd_comp_srcT f w t p ε h1 h2, Category.id_comp,
      shift_comp_t f w t p ε h1 h2]
  · rw [Category.assoc, gluingFwd_comp_tgtT f w t p ε h1 h2, Category.id_comp]
    exact comp_shift_eq_of_shift f w t p ε h1 h2 _ _ _ _ _ _ _ _ _ _ _
      (gluingBwd_comp_srcT f w t p ε h1 h2) (gluingBwd_comp_srcX f w t p ε h1 h2)
      (gluingBwd_comp_srcW f w t p ε h1 h2)
  · rw [Category.assoc, gluingFwd_comp_tgtX f w t p ε h1 h2,
      gluingBwd_comp_srcX f w t p ε h1 h2, Category.id_comp]

/-! ### The gluing isomorphism on the target, and the cocycle condition -/

variable (d : pullback (t ≫ w) w ≅ pullback w (t ≫ w))

variable (hd : pullback.fst (srcHom w t) f ≫ d.hom
    = gluingFwd f w t p ε h1 h2 ≫ pullback.fst (tgtHom w t) f)

include h1 h2 hd in
/-- The gluing isomorphism, composed with the projection to `T`, read after base change. -/
lemma pullbackFst_comp_d :
    pullback.fst (srcHom w t) f ≫ d.hom ≫ pullback.snd w (t ≫ w)
      = gluingFwd f w t p ε h1 h2 ≫ tgtT f w t := by
  rw [tgtT, ← Category.assoc, ← Category.assoc, hd]

include h1 h2 hd in
/-- **The action of the gluing isomorphism, read after base change along `f`.** For a point of
`T` and a point of `W` over one point of `Y`, the action of the gluing isomorphism on the base
change along `f` is the shift of that point of `T` onto that point of `W`. -/
lemma pullbackFst_comp_actPullback {Z : Scheme.{u}} (z : Z ⟶ Y)
    (v' : Z ⟶ T) (x' : Z ⟶ W) (hv : v' ≫ t ≫ w = x' ≫ w)
    (hτ' : (pullback.fst z f ≫ v') ≫ t ≫ w = pullback.snd z f ≫ f)
    (hω' : (pullback.fst z f ≫ x') ≫ w = pullback.snd z f ≫ f) :
    pullback.fst z f ≫ DescentDatum.actPullback (Over.mk t) d.hom v' x' hv
      = shift f w t p ε h1 (pullback.fst z f ≫ v') (pullback.snd z f)
          (pullback.fst z f ≫ x') hτ' hω' := by
  have hact : DescentDatum.actPullback (Over.mk t) d.hom v' x' hv
      = pullback.lift v' x' hv ≫ d.hom ≫ pullback.snd w (t ≫ w) := rfl
  have hin : (pullback.fst z f ≫ v') ≫ t ≫ w = (pullback.fst z f ≫ x') ≫ w := by
    rw [Category.assoc, Category.assoc, hv]
  have houter : pullback.lift (pullback.fst z f ≫ v') (pullback.fst z f ≫ x') hin ≫ srcHom w t
      = pullback.snd z f ≫ f := by
    rwa [srcHom, ← Category.assoc, pullback.lift_fst]
  set κ := pullback.lift (pullback.lift (pullback.fst z f ≫ v') (pullback.fst z f ≫ x') hin)
    (pullback.snd z f) houter
  have hκfst : κ ≫ pullback.fst (srcHom w t) f
      = pullback.lift (pullback.fst z f ≫ v') (pullback.fst z f ≫ x') hin :=
    pullback.lift_fst _ _ _
  have hκT : κ ≫ srcT f w t = pullback.fst z f ≫ v' := by
    rw [srcT, ← Category.assoc, hκfst, pullback.lift_fst]
  have hκW : κ ≫ srcW f w t = pullback.fst z f ≫ x' := by
    rw [srcW, ← Category.assoc, hκfst, pullback.lift_snd]
  have hκX : κ ≫ srcX f w t = pullback.snd z f := pullback.lift_snd _ _ _
  have hA : pullback.fst z f ≫ pullback.lift v' x' hv = κ ≫ pullback.fst (srcHom w t) f := by
    rw [hκfst]
    exact comp_pullback_lift (t ≫ w) w (pullback.fst z f) v' x' hv hin
  calc pullback.fst z f ≫ DescentDatum.actPullback (Over.mk t) d.hom v' x' hv
      = (pullback.fst z f ≫ pullback.lift v' x' hv) ≫ d.hom ≫ pullback.snd w (t ≫ w) := by
        rw [hact, Category.assoc]
    _ = κ ≫ pullback.fst (srcHom w t) f ≫ d.hom ≫ pullback.snd w (t ≫ w) := by
        rw [hA, Category.assoc]
    _ = κ ≫ gluingFwd f w t p ε h1 h2 ≫ tgtT f w t := by
        rw [pullbackFst_comp_d f w t p ε h1 h2 d hd]
    _ = κ ≫ shift f w t p ε h1 (srcT f w t) (srcX f w t) (srcW f w t) (srcT_comp f w t)
          (srcW_comp f w t) := by
        rw [gluingFwd_comp_tgtT f w t p ε h1 h2]
    _ = shift f w t p ε h1 (κ ≫ srcT f w t) (κ ≫ srcX f w t) (κ ≫ srcW f w t)
          (by rwa [hκT, hκX]) (by rwa [hκW, hκX]) :=
        comp_shift f w t p ε h1 κ _ _ _ _ _ _ _
    _ = shift f w t p ε h1 (pullback.fst z f ≫ v') (pullback.snd z f)
          (pullback.fst z f ≫ x') hτ' hω' :=
        shift_congr f w t p ε h1 hκT hκX hκW _ _ _ _

include h1 h2 hd in
/-- **The shift is the action of the gluing isomorphism.** In particular it does not depend on
the point of `X` through which it is computed: that independence is what the descent of the
gluing isomorphism along `f` expresses. -/
lemma shift_eq_actPullback {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (ω : Z ⟶ W)
    (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f) (hv : τ ≫ t ≫ w = ω ≫ w) :
    shift f w t p ε h1 τ x ω hτ hω
      = DescentDatum.actPullback (Over.mk t) d.hom τ ω hv := by
  have hμ : (𝟙 Z) ≫ (ω ≫ w) = x ≫ f := (Category.id_comp _).trans hω
  set μ := pullback.lift (𝟙 Z) x hμ
  have hμ1 : μ ≫ pullback.fst (ω ≫ w) f = 𝟙 Z := pullback.lift_fst _ _ _
  have hμ2 : μ ≫ pullback.snd (ω ≫ w) f = x := pullback.lift_snd _ _ _
  have hω' : (pullback.fst (ω ≫ w) f ≫ ω) ≫ w = pullback.snd (ω ≫ w) f ≫ f :=
    (Category.assoc _ _ _).trans pullback.condition
  have hτ' : (pullback.fst (ω ≫ w) f ≫ τ) ≫ t ≫ w = pullback.snd (ω ≫ w) f ≫ f := by
    rwa [Category.assoc, hv]
  have hμ' : ∀ {A : Scheme.{u}} (a : Z ⟶ A), μ ≫ pullback.fst (ω ≫ w) f ≫ a = a := fun a ↦ by
    rw [← Category.assoc, hμ1, Category.id_comp]
  calc shift f w t p ε h1 τ x ω hτ hω
      = shift f w t p ε h1 (μ ≫ pullback.fst (ω ≫ w) f ≫ τ)
          (μ ≫ pullback.snd (ω ≫ w) f) (μ ≫ pullback.fst (ω ≫ w) f ≫ ω)
          (by rwa [hμ', hμ2]) (by rwa [hμ', hμ2]) :=
        shift_congr f w t p ε h1 (hμ' τ).symm hμ2.symm (hμ' ω).symm _ _ _ _
    _ = μ ≫ shift f w t p ε h1 (pullback.fst (ω ≫ w) f ≫ τ) (pullback.snd (ω ≫ w) f)
          (pullback.fst (ω ≫ w) f ≫ ω) hτ' hω' :=
        (comp_shift f w t p ε h1 μ _ _ _ hτ' hω' _ _).symm
    _ = μ ≫ pullback.fst (ω ≫ w) f ≫ DescentDatum.actPullback (Over.mk t) d.hom τ ω hv := by
        rw [pullbackFst_comp_actPullback f w t p ε h1 h2 d hd (ω ≫ w) τ ω hv hτ' hω']
    _ = DescentDatum.actPullback (Over.mk t) d.hom τ ω hv := hμ' _

variable (hd1 : d.hom ≫ tgtHom w t = srcHom w t)

include h1 h2 hd hd1 in
/-- **The gluing isomorphism lies over the first projection of `W ×_Y W`.** This is the first
compatibility that `AlgebraicGeometry.DescentDatum.ofPullbackIso` asks for. -/
lemma d_hom_comp_fst [UniversalHomeomorphism f] [Etale w] :
    d.hom ≫ pullback.fst w (t ≫ w) = pullback.fst (t ≫ w) w ≫ t := by
  have hL : pullback.fst (srcHom w t) f ≫ d.hom ≫ pullback.fst w (t ≫ w)
      = srcT f w t ≫ t := by
    rw [← Category.assoc, hd, Category.assoc]
    exact gluingFwd_comp_tgtW f w t p ε h1 h2
  refine eq_of_pullbackFst_comp_eq_of_etale f (srcHom w t) w ?_ ?_ ?_
  · rwa [Category.assoc]
  · rw [Category.assoc, srcHom]
  · rw [hL, srcT, Category.assoc]

include h1 h2 hd hd1 in
/-- **The gluing isomorphism lies over the second projection of `W ×_Y W`.** This is the second
compatibility that `AlgebraicGeometry.DescentDatum.ofPullbackIso` asks for. -/
lemma d_hom_comp_snd [UniversalHomeomorphism f] [Etale w] :
    d.hom ≫ pullback.snd w (t ≫ w) ≫ t = pullback.snd (t ≫ w) w := by
  have hL : pullback.fst (srcHom w t) f ≫ d.hom ≫ pullback.snd w (t ≫ w) ≫ t
      = srcW f w t := by
    calc pullback.fst (srcHom w t) f ≫ d.hom ≫ pullback.snd w (t ≫ w) ≫ t
        = (pullback.fst (srcHom w t) f ≫ d.hom ≫ pullback.snd w (t ≫ w)) ≫ t := by
          rw [Category.assoc, Category.assoc]
      _ = (gluingFwd f w t p ε h1 h2 ≫ tgtT f w t) ≫ t := by
          rw [pullbackFst_comp_d f w t p ε h1 h2 d hd]
      _ = gluingFwd f w t p ε h1 h2 ≫ tgtT f w t ≫ t := Category.assoc _ _ _
      _ = srcW f w t := by
          rw [← Category.assoc, gluingFwd_comp_tgtT f w t p ε h1 h2,
            shift_comp_t f w t p ε h1 h2]
  refine eq_of_pullbackFst_comp_eq_of_etale f (srcHom w t) w ?_ ?_ ?_
  · rwa [Category.assoc, Category.assoc, ← tgtHom_eq w t]
  · exact (srcHom_eq w t).symm
  · rw [hL, srcW]

include h1 h2 hd hd1 in
/-- **The cocycle condition for the gluing isomorphism.** Both sides of the law that acting twice
is acting once are morphisms of schemes étale over `Y`, so faithfulness of base change reduces
the law to its base change along `f`, where it is the statement
`Stacks.Etale.shift_shift` that shifting twice is shifting once. -/
lemma actPullbackLaw_gluing [UniversalHomeomorphism f] [Etale w] [Etale t] :
    DescentDatum.ActPullbackLaw (f := w) (Over.mk t) d.hom := by
  have he₂ : d.hom ≫ pullback.snd w ((Over.mk t).hom ≫ w) ≫ (Over.mk t).hom
      = pullback.snd ((Over.mk t).hom ≫ w) w :=
    d_hom_comp_snd f w t p ε h1 h2 d hd hd1
  have hact : ∀ {Z : Scheme.{u}} (v : Z ⟶ T) (x : Z ⟶ W) (h : v ≫ t ≫ w = x ≫ w),
      DescentDatum.actPullback (Over.mk t) d.hom v x h ≫ t = x :=
    fun v x h ↦ DescentDatum.actPullback_comp_hom (Over.mk t) d.hom he₂ v x h
  have huniv : DescentDatum.actPullback (Over.mk t) d.hom
        (DescentDatum.actPullback (Over.mk t) d.hom
          (DescentDatum.tripleV (Over.mk t) (f := w))
          (DescentDatum.tripleX (Over.mk t) (f := w))
          (DescentDatum.tripleV_comp (Over.mk t)))
        (DescentDatum.tripleY (Over.mk t) (f := w))
        (DescentDatum.actPullback_comp_hom_comp (Over.mk t) d.hom he₂ _ _ _
          (DescentDatum.tripleV_comp (Over.mk t)) (DescentDatum.tripleX_comp (Over.mk t)))
      = DescentDatum.actPullback (Over.mk t) d.hom
        (DescentDatum.tripleV (Over.mk t) (f := w))
        (DescentDatum.tripleY (Over.mk t) (f := w))
        ((DescentDatum.tripleV_comp (Over.mk t)).trans
          (DescentDatum.tripleX_comp (Over.mk t))) := by
    set vV := DescentDatum.tripleV (Over.mk t) (f := w) with hvV
    set xX := DescentDatum.tripleX (Over.mk t) (f := w) with hxX
    set yY := DescentDatum.tripleY (Over.mk t) (f := w) with hyY
    have hxc : xX ≫ w = yY ≫ w := DescentDatum.tripleX_comp (Over.mk t)
    have hω : ∀ {x' : DescentDatum.tripleObj (Over.mk t) (f := w) ⟶ W}, x' ≫ w = yY ≫ w →
        (pullback.fst (yY ≫ w) f ≫ x') ≫ w = pullback.snd (yY ≫ w) f ≫ f := fun h ↦ by
      rw [Category.assoc, h, ← Category.assoc]
      exact pullback.condition (f := yY ≫ w) (g := f)
    have hωy := hω (x' := yY) rfl
    have hωx := hω hxc
    have hτ : ∀ {v' : DescentDatum.tripleObj (Over.mk t) (f := w) ⟶ T}, v' ≫ t ≫ w = xX ≫ w →
        (pullback.fst (yY ≫ w) f ≫ v') ≫ t ≫ w = pullback.snd (yY ≫ w) f ≫ f := fun hv ↦ by
      rw [Category.assoc, hv, ← Category.assoc]
      exact hωx
    refine eq_of_pullbackFst_comp_eq_of_etale f (yY ≫ w) (t ≫ w) ?_ ?_ ?_
    · rw [← Category.assoc, hact]
    · rw [← Category.assoc, hact]
    · rw [pullbackFst_comp_actPullback f w t p ε h1 h2 d hd (yY ≫ w) _ yY _
          (hτ (by rw [← Category.assoc, hact])) hωy,
        pullbackFst_comp_actPullback f w t p ε h1 h2 d hd (yY ≫ w) vV yY _
          (hτ (DescentDatum.tripleV_comp (Over.mk t))) hωy]
      have hinner := pullbackFst_comp_actPullback f w t p ε h1 h2 d hd (yY ≫ w) vV xX
        (DescentDatum.tripleV_comp (Over.mk t))
        (hτ (DescentDatum.tripleV_comp (Over.mk t))) hωx
      have hmid : shift f w t p ε h1
          (shift f w t p ε h1 (pullback.fst (yY ≫ w) f ≫ vV) (pullback.snd (yY ≫ w) f)
            (pullback.fst (yY ≫ w) f ≫ xX)
            (hτ (DescentDatum.tripleV_comp (Over.mk t))) hωx)
          (pullback.snd (yY ≫ w) f) (pullback.fst (yY ≫ w) f ≫ yY)
          (shift_comp f w t p ε h1 h2 _ _ _ _ _) hωy
        = shift f w t p ε h1 (pullback.fst (yY ≫ w) f ≫ vV) (pullback.snd (yY ≫ w) f)
            (pullback.fst (yY ≫ w) f ≫ yY)
            (hτ (DescentDatum.tripleV_comp (Over.mk t))) hωy :=
        shift_shift f w t p ε h1 h2 _ _ _ _ _ _ _ _
      refine Eq.trans ?_ hmid
      exact shift_congr f w t p ε h1 hinner rfl rfl _ _ _ _
  intro Z v x y hv hw hvx
  exact DescentDatum.actPullbackLaw_of_universal (Over.mk t) d.hom he₂ huniv v x y hv hw hvx

end Coord

/-! ### The descent -/

/-- **Descending an étale scheme through an affine étale covering of the target.** Let
`f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y` be étale, surjective and quasi-compact,
let `t : T ⟶ W` be étale and affine, and let `p : U ⟶ X` be a morphism of schemes. Suppose that
`T ×_Y X` and `U ×_Y W` are identified, over `X` by `h1` and over `W` by `h2`. Then `U` is, over
`X`, the base change along `f` of a scheme étale over `Y`.

This is the third step of the second proof of Stacks Project, Tag 04DZ. -/
theorem exists_etale_pullback_iso_of_etaleCoverComparison (f : X ⟶ Y)
    [UniversalHomeomorphism f] {W : Scheme.{u}} (w : W ⟶ Y) [Etale w] [Surjective w]
    [QuasiCompact w] {T : Scheme.{u}} (t : T ⟶ W) [Etale t] [IsAffineHom t]
    {U : Scheme.{u}} (p : U ⟶ X)
    (ε : pullback (t ≫ w) f ≅ pullback (p ≫ f) w)
    (h1 : ε.hom ≫ pullback.fst (p ≫ f) w ≫ p = pullback.snd (t ≫ w) f)
    (h2 : ε.hom ≫ pullback.snd (p ≫ f) w = pullback.fst (t ≫ w) f ≫ t) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  have hsrcEt : Etale (srcHom w t) := by
    rw [srcHom]
    infer_instance
  have htgtEt : Etale (tgtHom w t) := by
    rw [tgtHom]
    infer_instance
  -- the gluing isomorphism on the base change, and its descent to `Y`
  obtain ⟨d, hd1, hd2⟩ := exists_iso_of_pullback_iso f (srcHom w t) (tgtHom w t)
    ⟨gluingFwd f w t p ε h1 h2, gluingBwd f w t p ε h1 h2,
      gluingFwd_gluingBwd f w t p ε h1 h2, gluingBwd_gluingFwd f w t p ε h1 h2⟩
    (gluingFwd_comp_tgtX f w t p ε h1 h2)
  have hi1 := d_hom_comp_fst f w t p ε h1 h2 d hd2 hd1
  have hi2 := d_hom_comp_snd f w t p ε h1 h2 d hd2 hd1
  have hcoc : DescentDatum.ActPullbackLaw (f := w) (Over.mk t) d.hom :=
    actPullbackLaw_gluing f w t p ε h1 h2 d hd2 hd1
  -- the descent datum and its effectivity
  obtain ⟨C⟩ := DescentData.nonempty_chart_of_isFamilyEffective
    (DescentDatum.ofPullbackIso (Over.mk t) d hi1 hi2 hcoc)
    (DescentData.isFamilyEffective_of_isEffective
      (DescentDatum.isEffective_of_isAffineHom _ (inferInstanceAs (IsAffineHom t))))
  set vv := C.base.hom
  set pr : T ⟶ C.base.left := C.proj ()
  have hsq : IsPullback pr t vv w := C.isPullback ()
  have hcompat : d.hom ≫ pullback.snd w (t ≫ w) ≫ pr = pullback.fst (t ≫ w) w ≫ pr := by
    have hc := C.compat () ()
    rwa [DescentDatum.ofPullbackIso_gluingPullbackIso_hom (Over.mk t) d hi1 hi2 hcoc] at hc
  -- the descended scheme is étale over `Y`
  have hEt : Etale (pullback.snd vv w) := by
    rw [← hsq.isoPullback_inv_snd]
    infer_instance
  have hVEt : Etale vv :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨‹Surjective w›, inferInstanceAs (Flat w)⟩, ‹QuasiCompact w›⟩ hEt
  -- the covering of `X` obtained by base change
  set g := pullback.snd w f
  -- the three coordinate facts the comparison consumes
  have hsp : ∀ {Z : Scheme.{u}} (τ : Z ⟶ T) (x : Z ⟶ X) (ω : Z ⟶ W)
      (hτ : τ ≫ t ≫ w = x ≫ f) (hω : ω ≫ w = x ≫ f),
      shift f w t p ε h1 τ x ω hτ hω ≫ pr = τ ≫ pr := by
    intro Z τ x ω hτ hω
    have hv : τ ≫ t ≫ w = ω ≫ w := hτ.trans hω.symm
    rw [shift_eq_actPullback f w t p ε h1 h2 d hd2 τ x ω hτ hω hv]
    have hact : DescentDatum.actPullback (Over.mk t) d.hom τ ω hv
        = pullback.lift τ ω hv ≫ d.hom ≫ pullback.snd w (t ≫ w) := rfl
    rw [hact, Category.assoc, Category.assoc, hcompat, ← Category.assoc, pullback.lift_fst]
  have hText : ∀ {Z : Scheme.{u}} (τ₁ τ₂ : Z ⟶ T), τ₁ ≫ pr = τ₂ ≫ pr →
      τ₁ ≫ t = τ₂ ≫ t → τ₁ = τ₂ := fun τ₁ τ₂ ha hb ↦ hsq.hom_ext ha hb
  have huEq : ∀ {Z : Scheme.{u}} (τ₁ τ₂ : Z ⟶ T) (x : Z ⟶ X)
      (hτ₁ : τ₁ ≫ t ≫ w = x ≫ f) (hτ₂ : τ₂ ≫ t ≫ w = x ≫ f), τ₁ ≫ pr = τ₂ ≫ pr →
        uCoordOfPullbackIso f w t p ε τ₁ x hτ₁ = uCoordOfPullbackIso f w t p ε τ₂ x hτ₂ := by
    intro Z τ₁ τ₂ x hτ₁ hτ₂ hpr
    have hω : (τ₂ ≫ t) ≫ w = x ≫ f := (Category.assoc _ _ _).trans hτ₂
    have hs : shift f w t p ε h1 τ₁ x (τ₂ ≫ t) hτ₁ hω = τ₂ :=
      hText _ _ ((hsp _ _ _ _ _).trans hpr) (shift_comp_t f w t p ε h1 h2 _ _ _ _ _)
    exact ((uCoordOfPullbackIso_shift f w t p ε h1 τ₁ x (τ₂ ≫ t) hτ₁ hω
      (shift_comp f w t p ε h1 h2 _ _ _ _ _)).symm).trans
      (uCoordOfPullbackIso_congr f w t p ε hs rfl _ hτ₂)
  have htEq : ∀ {Z : Scheme.{u}} (u : Z ⟶ U) (ω₁ ω₂ : Z ⟶ W)
      (hu1 : u ≫ p ≫ f = ω₁ ≫ w) (hu2 : u ≫ p ≫ f = ω₂ ≫ w),
      tCoord f w t p ε u ω₁ hu1 ≫ pr = tCoord f w t p ε u ω₂ hu2 ≫ pr := by
    intro Z u ω₁ ω₂ hu1 hu2
    have hτ : tCoord f w t p ε u ω₁ hu1 ≫ t ≫ w = (u ≫ p) ≫ f := by
      rw [← Category.assoc, tCoord_comp f w t p ε h2, ← hu1, Category.assoc]
    have hω : ω₂ ≫ w = (u ≫ p) ≫ f := hu2.symm.trans (Category.assoc _ _ _).symm
    have hs : shift f w t p ε h1 (tCoord f w t p ε u ω₁ hu1) (u ≫ p) ω₂ hτ hω
        = tCoord f w t p ε u ω₂ hu2 :=
      tCoord_congr f w t p ε (uCoordOfPullbackIso_tCoord f w t p ε h1 u ω₁ hu1 hτ) rfl _ hu2
    rw [← hs, hsp]
  -- the coordinates of a point of the covering of the base change of the descended scheme
  set A1 := pullback.fst (pullback.snd vv f) g with hA1def
  set A2 := pullback.snd (pullback.snd vv f) g
  set B1 := pullback.fst p g with hB1def
  set B2 := pullback.snd p g
  have hAcond : A1 ≫ pullback.snd vv f = A2 ≫ g := pullback.condition
  have hBcond : B1 ≫ p = B2 ≫ g := pullback.condition
  have hcV : pullback.fst vv f ≫ vv = pullback.snd vv f ≫ f := pullback.condition
  have hcW : pullback.fst w f ≫ w = g ≫ f := pullback.condition
  have hnu : (A1 ≫ pullback.fst vv f) ≫ vv = (A2 ≫ pullback.fst w f) ≫ w := by
    rw [Category.assoc, hcV, Category.assoc, hcW, ← Category.assoc, ← Category.assoc, hAcond]
  set τ := hsq.lift (A1 ≫ pullback.fst vv f) (A2 ≫ pullback.fst w f) hnu
  have hτpr : τ ≫ pr = A1 ≫ pullback.fst vv f := hsq.lift_fst _ _ _
  have hτt : τ ≫ t = A2 ≫ pullback.fst w f := hsq.lift_snd _ _ _
  have hτc : τ ≫ t ≫ w = (A1 ≫ pullback.snd vv f) ≫ f := by
    rw [← Category.assoc, hτt, Category.assoc, hcW, ← Category.assoc, hAcond]
  have hψcond : uCoordOfPullbackIso f w t p ε τ (A1 ≫ pullback.snd vv f) hτc ≫ p = A2 ≫ g := by
    rw [uCoordOfPullbackIso_comp f w t p ε h1, hAcond]
  set ψ₀ := pullback.lift (uCoordOfPullbackIso f w t p ε τ (A1 ≫ pullback.snd vv f) hτc) A2 hψcond
  have hψ₀fst : ψ₀ ≫ B1 = uCoordOfPullbackIso f w t p ε τ (A1 ≫ pullback.snd vv f) hτc :=
    pullback.lift_fst _ _ _
  have hψ₀snd : ψ₀ ≫ B2 = A2 := pullback.lift_snd _ _ _
  -- the inverse comparison
  have hσcond : B1 ≫ p ≫ f = (B2 ≫ pullback.fst w f) ≫ w := by
    rw [← Category.assoc, hBcond, Category.assoc, Category.assoc, hcW]
  set σ := tCoord f w t p ε B1 (B2 ≫ pullback.fst w f) hσcond
  have hσt : σ ≫ t = B2 ≫ pullback.fst w f := tCoord_comp f w t p ε h2 _ _ _
  have hσc : (σ ≫ pr) ≫ vv = (B1 ≫ p) ≫ f := by
    rw [Category.assoc, hsq.w, ← Category.assoc, hσt, Category.assoc, hcW, ← Category.assoc,
      hBcond]
  have hσcond2 : pullback.lift (σ ≫ pr) (B1 ≫ p) hσc ≫ pullback.snd vv f = B2 ≫ g := by
    rw [pullback.lift_snd, hBcond]
  set ψ₁ := pullback.lift (pullback.lift (σ ≫ pr) (B1 ≫ p) hσc) B2 hσcond2
  have hψ₁fst : ψ₁ ≫ A1 = pullback.lift (σ ≫ pr) (B1 ≫ p) hσc := pullback.lift_fst _ _ _
  have hψ₁snd : ψ₁ ≫ A2 = B2 := pullback.lift_snd _ _ _
  -- the compatibility of the comparison with the canonical descent data
  have hcan : pullback.fst A1 A1 ≫ ψ₀ ≫ B1 = pullback.snd A1 A1 ≫ ψ₀ ≫ B1 := by
    have hk : pullback.fst A1 A1 ≫ A1 = pullback.snd A1 A1 ≫ A1 := pullback.condition
    have hx : pullback.fst A1 A1 ≫ A1 ≫ pullback.snd vv f
        = pullback.snd A1 A1 ≫ A1 ≫ pullback.snd vv f := by
      rw [← Category.assoc, hk, Category.assoc]
    have hpr1 : (pullback.fst A1 A1 ≫ τ) ≫ pr = (pullback.snd A1 A1 ≫ τ) ≫ pr := by
      rw [Category.assoc, Category.assoc, hτpr, ← Category.assoc, ← Category.assoc, hk]
    have e1 : (pullback.fst A1 A1 ≫ τ) ≫ t ≫ w
        = (pullback.fst A1 A1 ≫ A1 ≫ pullback.snd vv f) ≫ f := by
      rw [Category.assoc, hτc, ← Category.assoc]
    have e2 : (pullback.snd A1 A1 ≫ τ) ≫ t ≫ w
        = (pullback.fst A1 A1 ≫ A1 ≫ pullback.snd vv f) ≫ f := by
      rw [Category.assoc, hτc, ← Category.assoc, hx]
    have e3 : (pullback.snd A1 A1 ≫ τ) ≫ t ≫ w
        = (pullback.snd A1 A1 ≫ A1 ≫ pullback.snd vv f) ≫ f := by
      rw [Category.assoc, hτc, ← Category.assoc]
    rw [hψ₀fst]
    calc pullback.fst A1 A1 ≫ uCoordOfPullbackIso f w t p ε τ (A1 ≫ pullback.snd vv f) hτc
        = uCoordOfPullbackIso f w t p ε (pullback.fst A1 A1 ≫ τ)
            (pullback.fst A1 A1 ≫ A1 ≫ pullback.snd vv f) e1 :=
          comp_uCoordOfPullbackIso f w t p ε _ _ _ hτc e1
      _ = uCoordOfPullbackIso f w t p ε (pullback.snd A1 A1 ≫ τ)
            (pullback.fst A1 A1 ≫ A1 ≫ pullback.snd vv f) e2 := huEq _ _ _ e1 e2 hpr1
      _ = uCoordOfPullbackIso f w t p ε (pullback.snd A1 A1 ≫ τ)
            (pullback.snd A1 A1 ≫ A1 ≫ pullback.snd vv f) e3 :=
          uCoordOfPullbackIso_congr f w t p ε rfl hx e2 e3
      _ = pullback.snd A1 A1 ≫ uCoordOfPullbackIso f w t p ε τ (A1 ≫ pullback.snd vv f) hτc :=
          (comp_uCoordOfPullbackIso f w t p ε _ _ _ hτc e3).symm
  have hcan' : pullback.fst B1 B1 ≫ ψ₁ ≫ A1 = pullback.snd B1 B1 ≫ ψ₁ ≫ A1 := by
    have hk : pullback.fst B1 B1 ≫ B1 = pullback.snd B1 B1 ≫ B1 := pullback.condition
    have hA : ∀ k : pullback B1 B1 ⟶ pullback p g,
        (k ≫ B1) ≫ p ≫ f = (k ≫ B2 ≫ pullback.fst w f) ≫ w := by
      intro k
      rw [Category.assoc, hσcond, ← Category.assoc]
    have hA2' : (pullback.snd B1 B1 ≫ B1) ≫ p ≫ f
        = (pullback.fst B1 B1 ≫ B2 ≫ pullback.fst w f) ≫ w := by
      rw [← hk]
      exact hA _
    rw [hψ₁fst]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.lift_fst]
      calc pullback.fst B1 B1 ≫ σ ≫ pr
          = tCoord f w t p ε (pullback.fst B1 B1 ≫ B1)
              (pullback.fst B1 B1 ≫ B2 ≫ pullback.fst w f) (hA _) ≫ pr := by
            rw [← Category.assoc (pullback.fst B1 B1) σ pr,
              comp_tCoord f w t p ε (pullback.fst B1 B1) B1 (B2 ≫ pullback.fst w f) hσcond
                (hA _)]
        _ = tCoord f w t p ε (pullback.snd B1 B1 ≫ B1)
              (pullback.fst B1 B1 ≫ B2 ≫ pullback.fst w f) hA2' ≫ pr := by
            rw [tCoord_congr f w t p ε hk rfl (hA _) hA2']
        _ = tCoord f w t p ε (pullback.snd B1 B1 ≫ B1)
              (pullback.snd B1 B1 ≫ B2 ≫ pullback.fst w f) (hA _) ≫ pr :=
            htEq _ _ _ hA2' (hA _)
        _ = pullback.snd B1 B1 ≫ σ ≫ pr := by
            rw [← Category.assoc (pullback.snd B1 B1) σ pr,
              comp_tCoord f w t p ε (pullback.snd B1 B1) B1 (B2 ≫ pullback.fst w f) hσcond
                (hA _)]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc,
        ← Category.assoc, hk]
  -- the two halves of the comparison, and that they are mutually inverse
  obtain ⟨ψ, ⟨hψb, hψfst⟩, -⟩ := existsUnique_desc_of_surjective_flat_quasiCompact g
    (pullback.snd vv f) p ψ₀ hψ₀snd hcan
  obtain ⟨ψ', ⟨hψ'b, hψ'fst⟩, -⟩ := existsUnique_desc_of_surjective_flat_quasiCompact g
    p (pullback.snd vv f) ψ₁ hψ₁snd hcan'
  rw [← hA1def, ← hB1def] at hψfst hψ'fst
  have hr1 : ψ₀ ≫ ψ₁ ≫ A1 = A1 := by
    rw [hψ₁fst]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst]
      have hb2 : ψ₀ ≫ B2 ≫ pullback.fst w f = τ ≫ t := by
        rw [← Category.assoc, hψ₀snd, hτt]
      have hh : (ψ₀ ≫ B1) ≫ p ≫ f = (ψ₀ ≫ B2 ≫ pullback.fst w f) ≫ w := by
        rw [Category.assoc, hσcond, ← Category.assoc]
      have hωτ : (τ ≫ t) ≫ w = (A1 ≫ pullback.snd vv f) ≫ f := (Category.assoc τ t w).trans hτc
      have hh2 : uCoordOfPullbackIso f w t p ε τ (A1 ≫ pullback.snd vv f) hτc ≫ p ≫ f =
          (τ ≫ t) ≫ w := by
        rw [← Category.assoc, uCoordOfPullbackIso_comp f w t p ε h1]
        exact hωτ.symm
      have hστ : ψ₀ ≫ σ = τ := by
        calc ψ₀ ≫ σ
            = tCoord f w t p ε (ψ₀ ≫ B1) (ψ₀ ≫ B2 ≫ pullback.fst w f) hh :=
              comp_tCoord f w t p ε ψ₀ _ _ hσcond hh
          _ = tCoord f w t p ε
                (uCoordOfPullbackIso f w t p ε τ (A1 ≫ pullback.snd vv f) hτc) (τ ≫ t) hh2 :=
              tCoord_congr f w t p ε hψ₀fst hb2 hh hh2
          _ = τ := shift_self f w t p ε h1 h2 τ (A1 ≫ pullback.snd vv f) hτc hωτ
      rw [← Category.assoc, hστ, hτpr]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hψ₀fst,
        uCoordOfPullbackIso_comp f w t p ε h1]
  have hr2 : ψ₁ ≫ ψ₀ ≫ B1 = B1 := by
    rw [hψ₀fst]
    have hpr1 : (ψ₁ ≫ τ) ≫ pr = σ ≫ pr := by
      rw [Category.assoc, hτpr, ← Category.assoc, hψ₁fst, pullback.lift_fst]
    have ht1 : (ψ₁ ≫ τ) ≫ t = σ ≫ t := by
      rw [Category.assoc, hτt, ← Category.assoc, hψ₁snd, hσt]
    have hστ : ψ₁ ≫ τ = σ := hText _ _ hpr1 ht1
    have hxx : ψ₁ ≫ A1 ≫ pullback.snd vv f = B1 ≫ p := by
      rw [← Category.assoc, hψ₁fst, pullback.lift_snd]
    have hcc : (ψ₁ ≫ τ) ≫ t ≫ w = (ψ₁ ≫ A1 ≫ pullback.snd vv f) ≫ f := by
      rw [Category.assoc, hτc, ← Category.assoc]
    have hcc2 : σ ≫ t ≫ w = (B1 ≫ p) ≫ f := by
      rw [← Category.assoc, hσt, Category.assoc, hcW, ← Category.assoc, hBcond]
    calc ψ₁ ≫ uCoordOfPullbackIso f w t p ε τ (A1 ≫ pullback.snd vv f) hτc
        = uCoordOfPullbackIso f w t p ε (ψ₁ ≫ τ) (ψ₁ ≫ A1 ≫ pullback.snd vv f) hcc :=
          comp_uCoordOfPullbackIso f w t p ε ψ₁ _ _ hτc hcc
      _ = uCoordOfPullbackIso f w t p ε σ (B1 ≫ p) hcc2 :=
          uCoordOfPullbackIso_congr f w t p ε hστ hxx hcc hcc2
      _ = B1 := uCoordOfPullbackIso_tCoord f w t p ε h1 B1 (B2 ≫ pullback.fst w f) hσcond hcc2
  have hid1 : ψ ≫ ψ' = 𝟙 _ := by
    refine eq_of_pullbackFst_comp_eq g (pullback.snd vv f) ?_
    rw [← hA1def, Category.comp_id, ← Category.assoc, hψfst, Category.assoc, hψ'fst, hr1]
  have hid2 : ψ' ≫ ψ = 𝟙 U := by
    refine eq_of_pullbackFst_comp_eq g p ?_
    rw [← hB1def, Category.comp_id, ← Category.assoc, hψ'fst, Category.assoc, hψfst, hr2]
  exact ⟨C.base.left, vv, hVEt, ⟨ψ, ψ', hid1, hid2⟩, hψb⟩

end Stacks.Etale

end

end
