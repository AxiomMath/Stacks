module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Maps.SubmersiveClosed
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantPrincipalOpenGenericOrbits
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromSurjectiveUniversallyClosed

/-!
# Descending an invariant affine open along an integral morphism meeting every orbit

Let `G` be a groupoid scheme whose source and target maps are integral, and let
`g : U' ⟶ G.objects` be an integral morphism whose image meets every orbit of `G`.  An
invariant affine open of the restriction of `G` along `g` then produces an invariant affine
open of the object scheme of `G` containing the image of any of its points.

The construction is the saturation.  Writing `R̃ = U' ×_{g, U, t} G.arrows` with its first
projection `pr₀` to `U'` and with `h = pr₁ ≫ s` to the object scheme, both `pr₀` and `h` are
integral.  Hence the preimage `pr₀ ⁻¹ᵁ W'` of an affine open `W'` is affine, and its image
`W = h (pr₀ ⁻¹ᵁ W')` is the saturation `s (t ⁻¹ (g (W')))`, which is invariant.  Invariance of
`W'` is exactly what makes `pr₀ ⁻¹ᵁ W'` the full preimage `h ⁻¹ (W)`, so `W` is open because
`h` is integral and surjective, hence submersive, and then `W` is affine because it receives an
integral surjection from an affine scheme.

## Main results

* `AlgebraicGeometry.exists_invariant_affine_open_of_restriction_integral`:
  **[Stacks, Tag 0ABE]**, the descent of an invariant affine open along an integral morphism
  meeting every orbit.

## Implementation notes

The hypothesis that every orbit of `G` meets the image of `g` is spelled as the existence, for
each point `u` of the object scheme, of an arrow with source `u` and target in the image of
`g`; this is precisely surjectivity of `h`.

The restriction of `G` along `g` is taken to be an arbitrary
`AlgebraicGeometry.GroupoidScheme.Restriction G g`, so the statement applies in particular to
`AlgebraicGeometry.GroupoidScheme.restrict G g`.  Its object scheme is only *equal* to `U'`,
not identical to it, so the comparison isomorphism `eqToHom` appears when transporting opens
and points between the two.

## References

* [Stacks Project, Tag 0ABE](https://stacks.math.columbia.edu/tag/0ABE)
* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
* [Stacks Project, Tag 0AAU](https://stacks.math.columbia.edu/tag/0AAU)
* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- Transporting a point along an equality of schemes and back returns the point. -/
private lemma eqToHom_base_cast_symm {X Y : Scheme.{u}} (e : X = Y) (y : Y) :
    (eqToHom e) (e.symm ▸ y) = y := by
  cases e
  rfl

/-- Transporting a point of a scheme over a base along an equality and back along its inverse
returns the point. -/
private lemma over_eqToHom_symm_base_apply {X Y : Over S} (e : X = Y) (x : X.left) :
    (eqToHom e.symm).left ((eqToHom e).left x) = x := by
  cases e
  rfl

/-- A pair of points of two schemes over a base with the same image in a third one comes from a
point of the fibre product taken in schemes over the base. -/
private alias exists_point_of_pullback_over := exists_point_over_pullback

/-- Two composable points of the arrow scheme of a groupoid scheme have a composite, whose
source is the source of the second and whose target is the target of the first. -/
lemma exists_arrow_comp (G : Stacks.Groupoids.GroupoidScheme S) (a b : G.arrows.left)
    (hab : G.source.left a = G.target.left b) :
    ∃ c : G.arrows.left,
      G.source.left c = G.source.left b ∧ G.target.left c = G.target.left a := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_point_of_pullback_over G.source G.target a b hab
  refine ⟨G.comp.left p, ?_, ?_⟩
  · simpa [hp₂] using congrArg (fun k => k.left p) G.source_comp
  · simpa [hp₁] using congrArg (fun k => k.left p) G.target_comp

/-- Two arrows of a groupoid scheme with the same source give an arrow from the target of the
first to the target of the second. -/
private lemma exists_arrow_of_source_eq (G : Stacks.Groupoids.GroupoidScheme S)
    (a b : G.arrows.left) (hab : G.source.left b = G.source.left a) :
    ∃ c : G.arrows.left,
      G.source.left c = G.target.left a ∧ G.target.left c = G.target.left b := by
  obtain ⟨c, hcs, hct⟩ := exists_arrow_comp G b (G.inverse.left a) (by
    rw [hab]
    exact (congrArg (fun k : G.arrows ⟶ G.objects => k.left a) G.target_inverse).symm)
  exact ⟨c, hcs.trans (congrArg (fun k : G.arrows ⟶ G.objects => k.left a) G.source_inverse), hct⟩

/-- An arrow of a groupoid scheme whose source and target both lie in the image of the
restricting morphism comes from an arrow of the restricted groupoid. -/
private lemma exists_arrow_of_restriction (G : Stacks.Groupoids.GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (R : GroupoidScheme.Restriction G g)
    (x y : R.groupoid.objects.left) (a : G.arrows.left)
    (hs : G.source.left a = R.hom.mapObjects.left x)
    (ht : G.target.left a = R.hom.mapObjects.left y) :
    ∃ b : R.groupoid.arrows.left,
      R.groupoid.source.left b = x ∧ R.groupoid.target.left b = y := by
  let x₀ : U'.left := (eqToHom R.objects_eq).left x
  let y₀ : U'.left := (eqToHom R.objects_eq).left y
  have hx : R.hom.mapObjects.left x = g.left x₀ := by rw [R.mapObjects_eq]; rfl
  have hy : R.hom.mapObjects.left y = g.left y₀ := by rw [R.mapObjects_eq]; rfl
  obtain ⟨p₁, hp₁x, hp₁a⟩ := exists_point_of_pullback_over g G.target y₀ a
    (by rw [← hy, ← ht])
  obtain ⟨p₂, hp₂a, hp₂x⟩ := exists_point_of_pullback_over G.source g a x₀
    (by rw [hs, hx])
  obtain ⟨p, hpfst, hpsnd⟩ := exists_point_of_pullback_over
      (pullback.snd g G.target) (pullback.fst G.source g) p₁ p₂ (by rw [hp₁a, hp₂a])
  let hArrows := congrArg (fun A : Over S => A.left) R.arrows_eq
  have hcast : (eqToHom R.arrows_eq).left (hArrows.symm ▸ p) = p := by
    rw [show (eqToHom R.arrows_eq).left = eqToHom hArrows by simp]
    exact eqToHom_base_cast_symm hArrows p
  refine ⟨hArrows.symm ▸ p, ?_, ?_⟩
  · rw [R.source_eq]
    change (eqToHom R.objects_eq.symm).left
      ((restrictionSource G g).left ((eqToHom R.arrows_eq).left (hArrows.symm ▸ p))) = x
    rw [hcast]
    change (eqToHom R.objects_eq.symm).left ((pullback.snd G.source g).left
      ((pullback.snd (pullback.snd g G.target) (pullback.fst G.source g)).left p)) = x
    rw [hpsnd, hp₂x]
    exact over_eqToHom_symm_base_apply R.objects_eq x
  · rw [R.target_eq]
    change (eqToHom R.objects_eq.symm).left
      ((restrictionTarget G g).left ((eqToHom R.arrows_eq).left (hArrows.symm ▸ p))) = y
    rw [hcast]
    change (eqToHom R.objects_eq.symm).left ((pullback.fst g G.target).left
      ((pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left p)) = y
    rw [hpfst, hp₁x]
    exact over_eqToHom_symm_base_apply R.objects_eq y

/-- If every orbit of `G` meets the image of `g`, then the source map on
`U' ×_{g, U, t} G.arrows` is surjective. -/
private lemma surjective_pullback_snd_comp_source (G : Stacks.Groupoids.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects)
    (horbit : ∀ u : G.objects.left, ∃ u' : U'.left, ∃ r : G.arrows.left,
      G.source.left r = u ∧ G.target.left r = g.left u') :
    Surjective (pullback.snd g.left G.target.left ≫ G.source.left) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y, r, hsrc, htgt⟩ := horbit x
  obtain ⟨p, _, hp₁⟩ := Scheme.Pullback.exists_preimage_pullback y r htgt.symm
  exact ⟨p, (congrArg G.source.left hp₁).trans hsrc⟩

/-- A set whose preimage under an integral surjective morphism is an affine open is itself an
affine open. -/
private lemma exists_isOpen_isAffineOpen_of_preimage_eq {P X : Scheme.{u}} (h : P ⟶ X)
    [IsIntegralHom h] [Surjective h] {T : Set X} {V : P.Opens} (hV : IsAffineOpen V)
    (hT : h.base ⁻¹' T = V) : ∃ hTo : IsOpen T, IsAffineOpen (⟨T, hTo⟩ : X.Opens) := by
  have hTo : IsOpen T := by
    refine ((IsClosedMap.isQuotientMap (Scheme.Hom.isClosedMap h) h.continuous
      h.surjective).isCoinducing.isOpen_preimage).mp ?_
    rw [hT]
    exact V.2
  refine ⟨hTo, ?_⟩
  let W : X.Opens := ⟨T, hTo⟩
  have : IsAffine (h ⁻¹ᵁ W) := show IsAffineOpen (h ⁻¹ᵁ W) by
    convert hV using 1
    exact TopologicalSpace.Opens.ext hT
  have : Surjective (h ∣_ W) := ⟨fun y => by
    obtain ⟨x, hx⟩ := h.surjective y.1
    have hmem : x ∈ h ⁻¹ᵁ W := by
      change h.base x ∈ W
      rw [hx]
      exact y.2
    exact ⟨⟨x, hmem⟩, Subtype.ext ((morphismRestrict_base_coe h W ⟨x, hmem⟩).trans hx)⟩⟩
  exact Stacks.AffineFromUniversallyClosed.isAffine_of_surjective_universallyClosed (h ∣_ W)

/-- **[Stacks, Tag 0ABE]**.  Let `G` be a groupoid scheme over `S` whose source and target maps
are integral, let `g : U' ⟶ G.objects` be integral with image meeting every orbit of `G`, and
let `R` be the restriction of `G` along `g`.  A point of the object scheme of `R` contained in
an invariant affine open has its image in `G.objects` contained in an invariant affine open. -/
@[stacks 0ABE]
theorem exists_invariant_affine_open_of_restriction_integral
    (G : Stacks.Groupoids.GroupoidScheme S) [IsIntegralHom G.source.left]
    [IsIntegralHom G.target.left] {U' : Over S} {g : U' ⟶ G.objects} [IsIntegralHom g.left]
    (R : GroupoidScheme.Restriction G g)
    (horbit : ∀ u : G.objects.left, ∃ u' : U'.left, ∃ r : G.arrows.left,
      G.source.left r = u ∧ G.target.left r = g.left u')
    (u' : R.groupoid.objects.left) (W' : R.groupoid.objects.left.Opens)
    (hW'inv : Stacks.Groupoids.IsInvariantOpen R.groupoid W') (hW'aff : IsAffineOpen W')
    (hu' : u' ∈ W') :
    ∃ W : G.objects.left.Opens, Stacks.Groupoids.IsInvariantOpen G W ∧ IsAffineOpen W ∧
      R.hom.mapObjects.left u' ∈ W := by
  classical
  let fromU : U'.left ⟶ R.groupoid.objects.left := (eqToHom R.objects_eq.symm).left
  have hmap (z : U'.left) : R.hom.mapObjects.left (fromU z) = g.left z := by
    rw [R.mapObjects_eq]
    exact congrArg g.left (over_eqToHom_symm_base_apply R.objects_eq.symm z)
  have : IsIso fromU := by
    change IsIso ((Over.forget S).map (eqToHom R.objects_eq.symm))
    infer_instance
  let x' : U'.left := (eqToHom R.objects_eq).left u'
  have hfromU : fromU x' = u' := over_eqToHom_symm_base_apply R.objects_eq u'
  let V' : U'.left.Opens := fromU ⁻¹ᵁ W'
  have hV'aff : IsAffineOpen V' := hW'aff.preimage_of_isIso fromU
  have hx'V' : x' ∈ V' := show fromU x' ∈ W' from hfromU ▸ hu'
  let P : Scheme.{u} := pullback g.left G.target.left
  let pr₀ : P ⟶ U'.left := pullback.fst g.left G.target.left
  let pr₁ : P ⟶ G.arrows.left := pullback.snd g.left G.target.left
  let h : P ⟶ G.objects.left := pr₁ ≫ G.source.left
  let Wset : Set G.objects.left :=
    G.source.left.base '' (G.target.left.base ⁻¹' (g.left.base '' (V' : Set U'.left)))
  have hpr (p : P) : G.target.left (pr₁ p) = g.left (pr₀ p) := by
    simpa [pr₀, pr₁] using congrArg (fun k : P ⟶ G.objects.left => k p)
      (pullback.condition : pullback.fst g.left G.target.left ≫ g.left =
        pullback.snd g.left G.target.left ≫ G.target.left).symm
  have hpreSet : h.base ⁻¹' Wset = pr₀.base ⁻¹' (V' : Set U'.left) := by
    ext p
    refine ⟨?_, fun hp => ⟨pr₁ p, ⟨pr₀ p, hp, (hpr p).symm⟩, rfl⟩⟩
    rintro ⟨a, ⟨z, hzV, haz⟩, hsource⟩
    have hpa : G.source.left (pr₁ p) = G.source.left a := by simpa [h] using hsource.symm
    obtain ⟨c, hcs, hct⟩ := exists_arrow_of_source_eq G a (pr₁ p) hpa
    obtain ⟨b, hbs, hbt⟩ := exists_arrow_of_restriction G g R (fromU z) (fromU (pr₀ p)) c
      ((hcs.trans haz.symm).trans (hmap z).symm)
      ((hct.trans (hpr p)).trans (hmap (pr₀ p)).symm)
    change fromU (pr₀ p) ∈ W'
    exact hbt ▸ hW'inv b (hbs ▸ hzV)
  have : Surjective h := surjective_pullback_snd_comp_source G g horbit
  obtain ⟨hWo, hWaff⟩ :=
    exists_isOpen_isAffineOpen_of_preimage_eq h (hV'aff.preimage pr₀) hpreSet
  refine ⟨⟨Wset, hWo⟩, ?_, hWaff, ?_⟩
  · rintro a ⟨b, ⟨z, hzV, hbz⟩, hbs⟩
    obtain ⟨c, hcs, hct⟩ := exists_arrow_of_source_eq G a b hbs
    exact ⟨c, ⟨z, hzV, hbz.trans hct.symm⟩, hcs⟩
  · change R.hom.mapObjects.left u' ∈ Wset
    rw [← hfromU, hmap x']
    exact ⟨G.identity.left (g.left x'), ⟨x', hx'V',
      (congrArg (fun k : G.objects ⟶ G.objects => k.left (g.left x')) G.target_identity).symm⟩,
      congrArg (fun k : G.objects ⟶ G.objects => k.left (g.left x')) G.source_identity⟩

end AlgebraicGeometry

end
