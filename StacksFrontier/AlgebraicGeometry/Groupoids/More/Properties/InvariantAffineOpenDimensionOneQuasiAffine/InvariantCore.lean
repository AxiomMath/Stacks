module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.AffineQuasiCompactImmersion
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.FiniteGroupoidThickening
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantPrincipalOpenGenericOrbits
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber

/-!
# The invariant core of an open of a groupoid scheme

This file contains the first part of the proof of the quasi-affine case of [Stacks, Tag 0ABI],
whose main result is in `InvariantAffineOpenDimensionOneQuasiAffine.NoetherianQuasiAffine`:
general facts about the restriction `AlgebraicGeometry.GroupoidScheme.restrict` of a groupoid
scheme along a morphism, and the invariant core of an open.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isAffineOpen_invariantCore_of_norm_of_invariant_complement`:
  Steps 8 to 10 of the proof of [Stacks, Tag 0ABI].

## Implementation notes

* Steps 8 to 10 are `isAffineOpen_invariantCore_of_norm_of_invariant_complement`. The open `V`
  of the source is realized as the invariant core of the nonvanishing locus of `h`, that is, as
  the complement of the saturation of its complement. This is how openness is obtained here:
  the invariant core is open because the source map is closed, which replaces the source's
  argument from constructibility and stability under generalization ([Stacks, Tag 0542]). Its
  affineness is [Stacks, Tag 0ABH] applied to the immersion into the nonvanishing locus of `h`,
  after the norm along the finite locally free source map
  (`Stacks.Divisors.finiteLocallyFreeNorm`, [Stacks, Tag 0BD2]) identifies the part of it inside
  the locus of `f` with a principal open of that affine open. The invariance of that norm
  ([Stacks, Tag 03BH]) is not needed: what the source uses it for -- that the locus it cuts out
  is invariant -- holds by construction of the invariant core, and the norm is used here only to
  exhibit that locus as a principal open.

## References

* [Stacks Project, Tag 0ABI](https://stacks.math.columbia.edu/tag/0ABI)
* [Stacks Project, Tag 0ABH](https://stacks.math.columbia.edu/tag/0ABH)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The nonvanishing locus of the norm of a section along a finite morphism is the complement of
the image of the vanishing locus of that section: the norm vanishes at an image point of a zero
of the section, and over the open complement the section is invertible, so its norm is too. -/
private lemma basicOpen_norm_eq_compl_image {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (N : Stacks.Norm.MorphismNormMap f)
    (s : Γ(X, f ⁻¹ᵁ (⊤ : Y.Opens))) :
    (Y.basicOpen (N.app ⊤ s) : Set Y) =
      (f '' (X.basicOpen s : Set X)ᶜ)ᶜ := by
  classical
  let V : Y.Opens := ⟨(f '' (X.basicOpen s : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ (X.basicOpen s).isOpen.isClosed_compl).isOpen_compl⟩
  have hle : f ⁻¹ᵁ V ≤ X.basicOpen s := by
    intro x hx
    by_contra hxs
    exact hx ⟨x, hxs, rfl⟩
  let i : V ⟶ ⊤ := homOfLE le_top
  let k : f ⁻¹ᵁ V ⟶ X.basicOpen s := homOfLE hle
  have hsunit : IsUnit
      (X.presheaf.map ((Opens.map f.base).map i).op s) := by
    have hunit := X.toRingedSpace.isUnit_res_basicOpen s
    have hunit' := hunit.map (X.presheaf.map k.op).hom
    convert hunit' using 1
    show X.presheaf.map ((Opens.map f.base).map i).op s =
      X.presheaf.map k.op (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s)
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  have hnunit := hsunit.map (N.app V)
  rw [N.naturality i s] at hnunit
  have hVN : V ≤ Y.basicOpen (N.app ⊤ s) := by
    have heq := Y.basicOpen_of_isUnit hnunit
    rw [Y.basicOpen_res] at heq
    exact inf_eq_left.mp heq
  refine Set.Subset.antisymm (fun y hy => ?_) hVN
  rintro ⟨x, hxs, rfl⟩
  have hzero := N.app_eq_zero_at_image s x (by simp)
    ((X.evaluation_eq_zero_iff_notMem_basicOpen x (by simp) s).2 hxs)
  exact ((Y.evaluation_ne_zero_iff_mem_basicOpen (f x) (by simp) _).2 hy) hzero

/-- Transport of a point along an equality of schemes over a base is the point obtained by
applying the induced morphism. -/
lemma over_eqToHom_apply_in_restriction {S : Scheme.{u}} {X Y : Over S}
    (e : X = Y) (y : Y.left) :
    (eqToHom e.symm).left y = e.symm ▸ y := by
  cases e
  rfl

/-- The orbit of a point of the object scheme is finite when the source map is finite: it is
contained in the image under the target map of the fibre of the source map. -/
lemma orbit_finite {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] (x : G.objects.left) :
    {y : G.objects.left | ∃ r : G.arrows.left,
      G.source.left.base r = x ∧ G.target.left.base r = y}.Finite := by
  refine ((G.source.left.finite_preimage_singleton x).image G.target.left.base).subset ?_
  rintro y ⟨r, hr, rfl⟩
  exact ⟨r, hr, rfl⟩

/-- Two composable arrows of a groupoid scheme, given pointwise, compose: there is an arrow whose
source is the source of the second and whose target is the target of the first. -/
alias exists_comp_point := AlgebraicGeometry.exists_arrow_comp

/-- The underlying morphism of schemes of a transport morphism between equal objects over a base
is an isomorphism. -/
lemma isIso_over_eqToHom_left {S : Scheme.{u}} {X Y : Over S} (e : X = Y) :
    IsIso (eqToHom e).left := by
  cases e
  show IsIso (𝟙 X.left)
  infer_instance

/-- A base change of a finite morphism of schemes over a base is finite, for the second
projection out of the fibre product. -/
@[ega "II 1.5.5" "special case"]
lemma finite_over_pullback_snd {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite f.left] :
    IsFinite (pullback.snd f g).left := by
  have sq := (IsPullback.of_hasPullback f g).map (Over.forget S)
  exact MorphismProperty.of_isPullback sq (show IsFinite f.left from inferInstance)

/-- A base change of a finite morphism of schemes over a base is finite, for the first projection
out of the fibre product. -/
@[ega "II 1.5.5" "finite base morphism"]
private lemma finite_over_pullback_fst {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite g.left] :
    IsFinite (pullback.fst f g).left := by
  have sq := (IsPullback.of_hasPullback f g).map (Over.forget S)
  exact MorphismProperty.of_isPullback sq.flip (show IsFinite g.left from inferInstance)

/-- The source and target maps of a groupoid scheme realizing a restriction along a finite
morphism are finite, since they are composites of base changes of the finite source, target and
restricting maps. -/
lemma finite_restriction_maps {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    {U' : Over S} (g : U' ⟶ G.objects) [IsFinite g.left]
    (R : AlgebraicGeometry.GroupoidScheme.Restriction G g) :
    IsFinite R.groupoid.source.left ∧ IsFinite R.groupoid.target.left := by
  have := isIso_over_eqToHom_left R.arrows_eq
  have := isIso_over_eqToHom_left R.objects_eq.symm
  have : IsFinite (pullback.snd g G.target).left := finite_over_pullback_snd g G.target
  have : IsFinite (pullback.fst G.source g).left := finite_over_pullback_fst G.source g
  have : IsFinite (pullback.snd G.source g).left := finite_over_pullback_snd G.source g
  have : IsFinite (pullback.fst g G.target).left := finite_over_pullback_fst g G.target
  have : IsFinite (pullback.snd (pullback.snd g G.target)
      (pullback.fst G.source g)).left := finite_over_pullback_snd _ _
  have : IsFinite (pullback.fst (pullback.snd g G.target)
      (pullback.fst G.source g)).left := finite_over_pullback_fst _ _
  have : IsFinite (AlgebraicGeometry.restrictionSource G g).left := by
    show IsFinite ((pullback.snd (pullback.snd g G.target)
      (pullback.fst G.source g)).left ≫ (pullback.snd G.source g).left)
    infer_instance
  have : IsFinite (AlgebraicGeometry.restrictionTarget G g).left := by
    show IsFinite ((pullback.fst (pullback.snd g G.target)
      (pullback.fst G.source g)).left ≫ (pullback.fst g G.target).left)
    infer_instance
  rw [R.source_eq, R.target_eq]
  simp only [Over.comp_left]
  exact ⟨inferInstance, inferInstance⟩

/-- Transporting a point along an equality of objects over a base and then back is the
identity. -/
private lemma over_eqToHom_left_symm_apply {S : Scheme.{u}} {X Y : Over S} (e : X = Y)
    (y : Y.left) : (eqToHom e).left ((eqToHom e.symm).left y) = y := by
  cases e
  rfl

/-- An arrow of the ambient groupoid between two points in the image of the restricting map comes
from an arrow of the restricted groupoid between the corresponding points. -/
private lemma exists_restriction_arrow {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    (x y : U'.left) (r : G.arrows.left)
    (hs : G.source.left r = g.left x) (ht : G.target.left r = g.left y) :
    ∃ q : R.groupoid.arrows.left,
      R.groupoid.source.left q = (eqToHom R.objects_eq.symm).left x ∧
      R.groupoid.target.left q = (eqToHom R.objects_eq.symm).left y := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_point_over_pullback g G.target y r ht.symm
  obtain ⟨b, hb₁, hb₂⟩ := exists_point_over_pullback G.source g r x hs
  obtain ⟨p, hp₁, hp₂⟩ := exists_point_over_pullback
    (pullback.snd g G.target) (pullback.fst G.source g) a b (ha₂.trans hb₁.symm)
  refine ⟨(eqToHom R.arrows_eq.symm).left p, ?_, ?_⟩
  · rw [R.source_eq]
    show (eqToHom R.objects_eq.symm).left
      ((pullback.snd G.source g).left
        ((pullback.snd (pullback.snd g G.target) (pullback.fst G.source g)).left
          ((eqToHom R.arrows_eq).left ((eqToHom R.arrows_eq.symm).left p)))) = _
    rw [over_eqToHom_left_symm_apply R.arrows_eq p, hp₂, hb₂]
  · rw [R.target_eq]
    show (eqToHom R.objects_eq.symm).left
      ((pullback.fst g G.target).left
        ((pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left
          ((eqToHom R.arrows_eq).left ((eqToHom R.arrows_eq.symm).left p)))) = _
    rw [over_eqToHom_left_symm_apply R.arrows_eq p, hp₁, ha₁]

/-- For an open immersion with invariant image, the projection of the arrow scheme of the
restriction onto the source preimage is an isomorphism: invariance makes the target of an arrow
with source in the image lie in the image, which produces the inverse. -/
private lemma isIso_restriction_projection_of_invariant_open
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) [IsOpenImmersion g.left]
    (hg : Stacks.Groupoids.IsInvariantSet G (Set.range g.left)) :
    IsIso (pullback.snd (pullback.snd g G.target) (pullback.fst G.source g)).left := by
  have : IsOpenImmersion (pullback.snd g G.target).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback g G.target).map (Over.forget S))
      (show IsOpenImmersion g.left from inferInstance)
  have hopen : IsOpenImmersion
      (pullback.snd (pullback.snd g G.target) (pullback.fst G.source g)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback (pullback.snd g G.target) (pullback.fst G.source g)).map
        (Over.forget S)) (show IsOpenImmersion (pullback.snd g G.target).left from inferInstance)
  refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hopen, ⟨fun b => ?_⟩⟩
  let r := (pullback.fst G.source g).left b
  have hs : G.source.left r = g.left ((pullback.snd G.source g).left b) :=
    congrArg (fun k : pullback G.source g ⟶ G.objects => k.left b) pullback.condition
  obtain ⟨y, hy⟩ := hg r ⟨(pullback.snd G.source g).left b, hs.symm⟩
  obtain ⟨a, _, har⟩ := exists_point_over_pullback g G.target y r hy
  obtain ⟨p, _, hpb⟩ := exists_point_over_pullback
    (pullback.snd g G.target) (pullback.fst G.source g) a b har
  exact ⟨p, hpb⟩

/-- For an open immersion with invariant image, a morphism property stable under isomorphisms
holds for the source map of a groupoid scheme realizing the restriction exactly when it holds
for the base change of the source map along the restricting morphism. -/
lemma restriction_source_property_iff_of_invariant_open
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) [IsOpenImmersion g.left]
    (hg : Stacks.Groupoids.IsInvariantSet G (Set.range g.left))
    (R : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P R.groupoid.source.left ↔ P (pullback.snd G.source g).left := by
  have := isIso_over_eqToHom_left R.arrows_eq
  have := isIso_over_eqToHom_left R.objects_eq.symm
  have := isIso_restriction_projection_of_invariant_open G g hg
  rw [R.source_eq]
  simp only [Over.comp_left, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  show P ((pullback.snd (pullback.snd g G.target) (pullback.fst G.source g)).left ≫
    (pullback.snd G.source g).left) ↔ _
  exact P.cancel_left_of_respectsIso _ _

/-- A morphism property stable under isomorphisms holds for the source map of a groupoid scheme
exactly when it holds for its target map, because the inverse is an isomorphism carrying one to
the other. -/
lemma groupoid_source_property_iff_target {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P G.source.left ↔ P G.target.left := by
  have : IsIso G.inverse.left := groupoidInverse_left_isIso G
  rw [← G.source_inverse]
  show P G.source.left ↔ P (G.inverse.left ≫ G.source.left)
  exact (P.cancel_left_of_respectsIso _ _).symm

/-- An arrow of the ambient groupoid between the images of two points of the restricted groupoid
comes from an arrow of the restricted groupoid between those points. -/
lemma exists_restriction_arrow_of_mapObjects
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    (x y : R.groupoid.objects.left) (r : G.arrows.left)
    (hs : G.source.left r = R.hom.mapObjects.left x)
    (ht : G.target.left r = R.hom.mapObjects.left y) :
    ∃ q : R.groupoid.arrows.left,
      R.groupoid.source.left q = x ∧ R.groupoid.target.left q = y := by
  rw [R.mapObjects_eq] at hs ht
  obtain ⟨q, hqs, hqt⟩ := exists_restriction_arrow G g R
    ((eqToHom R.objects_eq).left x) ((eqToHom R.objects_eq).left y) r hs ht
  exact ⟨q, hqs.trans (over_eqToHom_left_symm_apply R.objects_eq.symm x),
    hqt.trans (over_eqToHom_left_symm_apply R.objects_eq.symm y)⟩

/-- The image of an invariant subset of the objects of a restricted groupoid is invariant in the
ambient groupoid, provided the image of the restricting map is itself invariant. -/
lemma invariant_image_of_restriction
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    (hR : Stacks.Groupoids.IsInvariantSet G (Set.range R.hom.mapObjects.left))
    (V : Set R.groupoid.objects.left) (hV : Stacks.Groupoids.IsInvariantSet R.groupoid V) :
    Stacks.Groupoids.IsInvariantSet G (R.hom.mapObjects.left '' V) := by
  intro r hr
  obtain ⟨x, hx, hrx⟩ := hr
  obtain ⟨y, hry⟩ := hR r ⟨x, hrx⟩
  obtain ⟨q, hqs, hqt⟩ := exists_restriction_arrow_of_mapObjects G g R x y r
    hrx.symm hry.symm
  exact ⟨y, hqt ▸ hV q (hqs ▸ hx), hry⟩

/-- A morphism property stable under isomorphisms holds for the map on objects of a groupoid
scheme realizing a restriction exactly when it holds for the restricting morphism. -/
lemma restriction_mapObjects_property_iff
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P R.hom.mapObjects.left ↔ P g.left := by
  have := isIso_over_eqToHom_left R.objects_eq
  rw [R.mapObjects_eq]
  show P ((eqToHom R.objects_eq).left ≫ g.left) ↔ _
  exact P.cancel_left_of_respectsIso _ _

/-- The image of the map on objects of a groupoid scheme realizing a restriction is the image of
the restricting morphism. -/
lemma range_restriction_mapObjects
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction G g) :
    Set.range R.hom.mapObjects.left = Set.range g.left := by
  have hsurj : Function.Surjective (eqToHom R.objects_eq).left := by
    intro x
    exact ⟨_, over_eqToHom_left_symm_apply R.objects_eq x⟩
  rw [R.mapObjects_eq]
  show Set.range (g.left ∘ (eqToHom R.objects_eq).left) = _
  rw [Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- The largest invariant subset of an open subscheme of the objects: the set of points all of
whose outgoing arrows have target in the open. It is open because the source map is closed and
the target map continuous. -/
def invariantCore {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] (V : G.objects.left.Opens) : G.objects.left.Opens :=
  ⟨(G.source.left '' (G.target.left ⁻¹' (V : Set G.objects.left)ᶜ))ᶜ,
    (G.source.left.isClosedMap _
      (V.isOpen.isClosed_compl.preimage G.target.left.continuous)).isOpen_compl⟩

/-- A point lies in the invariant core of an open exactly when every arrow with that source has
its target in the open. -/
lemma mem_invariantCore_iff {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.source.left]
    (V : G.objects.left.Opens) (x : G.objects.left) :
    x ∈ invariantCore G V ↔
      ∀ r : G.arrows.left, G.source.left r = x → G.target.left r ∈ V := by
  classical
  show (¬ ∃ r, G.target.left r ∉ V ∧ G.source.left r = x) ↔ _
  exact ⟨fun h r hr => not_not.mp fun ht => h ⟨r, ht, hr⟩, fun h ⟨r, ht, hr⟩ => ht (h r hr)⟩

/-- The invariant core of an open is contained in it, as witnessed by the identity arrow. -/
private lemma invariantCore_le {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.source.left]
    (V : G.objects.left.Opens) : invariantCore G V ≤ V := by
  intro x hx
  have hs : G.source.left (G.identity.left x) = x :=
    congrArg (fun f : G.objects ⟶ G.objects => f.left x) G.source_identity
  have ht : G.target.left (G.identity.left x) = x :=
    congrArg (fun f : G.objects ⟶ G.objects => f.left x) G.target_identity
  exact ht ▸ (mem_invariantCore_iff G V x).1 hx (G.identity.left x) hs

/-- The invariant core of an open is invariant: composing an arrow out of the target with the
given arrow exhibits the required membership. -/
lemma invariantCore_invariant {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.source.left]
    (V : G.objects.left.Opens) : Stacks.Groupoids.IsInvariantOpen G (invariantCore G V) := by
  intro r hr
  refine (mem_invariantCore_iff G V _).2 fun q hq => ?_
  obtain ⟨c, hcs, hct⟩ := exists_comp_point G q r hq
  exact hct ▸ (mem_invariantCore_iff G V _).1 hr c hcs

/-- Inside an affine open `K` the invariant core of the nonvanishing locus of a global function
is cut out by a single function, namely the norm along the source map restricted to `K` of the
pullback of that function along the target map. -/
private lemma exists_basicOpen_eq_preimage_invariantCore
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.source.left]
    (K : G.objects.left.Opens) (N : Stacks.Norm.MorphismNormMap (G.source.left ∣_ K))
    (a : Γ(G.objects.left, ⊤)) :
    ∃ g : Γ(K.toScheme, ⊤),
      K.ι ⁻¹ᵁ invariantCore G (G.objects.left.basicOpen a) = K.toScheme.basicOpen g := by
  let F := G.source.left ∣_ K
  let T := (G.source.left ⁻¹ᵁ K).ι ≫ G.target.left
  let s : Γ((G.source.left ⁻¹ᵁ K).toScheme, F ⁻¹ᵁ ⊤) := T.appLE ⊤ _ (by simp) a
  refine ⟨N.app ⊤ s, ?_⟩
  apply Opens.ext
  rw [basicOpen_norm_eq_compl_image F N s]
  have hbasic : (G.source.left ⁻¹ᵁ K).toScheme.basicOpen s =
      T ⁻¹ᵁ G.objects.left.basicOpen a :=
    (Scheme.basicOpen_appLE T (F ⁻¹ᵁ ⊤) ⊤ (by simp) a).trans (by simp)
  rw [hbasic]
  have hF (r : (G.source.left ⁻¹ᵁ K).toScheme) :
      (F r).val = G.source.left r.val :=
    congrArg (fun f => f r) (morphismRestrict_ι G.source.left K)
  ext x
  show (¬ ∃ r, G.target.left r ∉ G.objects.left.basicOpen a ∧
    G.source.left r = x.1) ↔
    ¬ ∃ r : (G.source.left ⁻¹ᵁ K).toScheme,
      T r ∉ G.objects.left.basicOpen a ∧ F r = x
  apply not_congr
  constructor
  · rintro ⟨r, hr, heq⟩
    have hrK : r ∈ G.source.left ⁻¹ᵁ K := by
      show G.source.left r ∈ K
      rw [heq]
      exact x.2
    exact ⟨⟨r, hrK⟩, hr, Subtype.ext ((hF _).trans heq)⟩
  · rintro ⟨r, hr, heq⟩
    exact ⟨r.1, hr, (hF r).symm.trans (congrArg Subtype.val heq)⟩

/-- The intersection of an affine open with the invariant core of the nonvanishing locus of a
global function is affine, being a principal open of that affine open. -/
private lemma isAffineOpen_inf_invariantCore_of_norm
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.source.left]
    (K : G.objects.left.Opens) (hK : IsAffineOpen K)
    (N : Stacks.Norm.MorphismNormMap (G.source.left ∣_ K))
    (a : Γ(G.objects.left, ⊤)) :
    IsAffineOpen (K ⊓ invariantCore G (G.objects.left.basicOpen a)) := by
  obtain ⟨g, hg⟩ := exists_basicOpen_eq_preimage_invariantCore G K N a
  have : IsAffine K.toScheme := hK
  have himg := ((isAffineOpen_top K.toScheme).basicOpen g).image_of_isOpenImmersion K.ι
  rw [← hg, K.ι.image_preimage_eq_opensRange_inf] at himg
  simpa using himg

/-- A quasi-compact immersion into an affine scheme whose restriction over the nonvanishing locus
of a global function is affine, and the rest of whose image is closed, has affine source. This
is [Stacks, Tag 0ABH] phrased for a global section instead of a ring element. -/
private lemma isAffine_of_isImmersion_of_basicOpen_section
    {X Y : Scheme.{u}} [IsAffine Y] (j : X ⟶ Y) [IsImmersion j] [QuasiCompact j]
    (f : Γ(Y, ⊤)) (hD : IsAffineOpen (j ⁻¹ᵁ Y.basicOpen f))
    (hclosed : IsClosed (Set.range j ∩ (Y.basicOpen f : Set Y)ᶜ)) : IsAffine X := by
  let e := Y.isoSpec
  have he : Function.Bijective e.hom :=
    ⟨fun a b h => by simpa using congrArg e.inv h, fun y => ⟨e.inv y, by simp⟩⟩
  apply AlgebraicGeometry.isAffine_of_isImmersion_of_isAffineOpen_preimage_basicOpen (j ≫ e.hom) f
  · have hcomp := Scheme.Hom.comp_preimage j e.hom (PrimeSpectrum.basicOpen f)
    rw [show e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f = Y.basicOpen f from
      Y.toSpecΓ_preimage_basicOpen f] at hcomp
    exact hcomp.symm ▸ hD
  · have hbasic : e.hom ⁻¹' ((Spec Γ(Y, ⊤)).basicOpen
        ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv f) : Set (Spec Γ(Y, ⊤))) =
          (Y.basicOpen f : Set Y) := by
      rw [basicOpen_eq_of_affine]
      exact congrArg Opens.carrier (Y.toSpecΓ_preimage_basicOpen f)
    have hpre : e.hom ⁻¹' Set.range (j ≫ e.hom) = Set.range j := by
      ext y
      exact ⟨fun ⟨x, hx⟩ => ⟨x, he.1 hx⟩, fun ⟨x, hx⟩ => ⟨x, by rw [← hx]; rfl⟩⟩
    have hEq : Set.range (j ≫ e.hom) ∩ ((Spec Γ(Y, ⊤)).basicOpen
        ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv f) : Set _)ᶜ =
          e.hom '' (Set.range j ∩ (Y.basicOpen f : Set Y)ᶜ) := by
      rw [← hpre, ← hbasic, ← Set.preimage_compl, ← Set.preimage_inter]
      exact (Set.image_preimage_eq _ he.2).symm
    exact hEq ▸ e.hom.isClosedMap _ hclosed

/-- The invariant core of the nonvanishing locus of a function `h` is affine, given that the
nonvanishing loci of `h` and of a second function `f` are affine and that an arrow whose source
lies outside the locus of `f` but inside that of `h` has its target inside the locus of `h`.
This is the affineness of the open constructed in the last two steps of the source's proof. -/
lemma isAffineOpen_invariantCore_of_norm_of_invariant_complement
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsNoetherian G.objects.left]
    (f h : Γ(G.objects.left, ⊤))
    (hf : IsAffineOpen (G.objects.left.basicOpen f))
    (hh : IsAffineOpen (G.objects.left.basicOpen h))
    (N : Stacks.Norm.MorphismNormMap (G.source.left ∣_ G.objects.left.basicOpen f))
    (hres : ∀ r : G.arrows.left,
      G.source.left r ∈ G.objects.left.basicOpen h →
      G.source.left r ∉ G.objects.left.basicOpen f →
      G.target.left r ∈ G.objects.left.basicOpen h) :
    IsAffineOpen (invariantCore G (G.objects.left.basicOpen h)) := by
  let H := G.objects.left.basicOpen h
  let O := invariantCore G H
  let j : O.toScheme ⟶ H.toScheme :=
    G.objects.left.homOfLE (invariantCore_le G H)
  have : IsAffine H.toScheme := hh
  let fH := H.ι.appTop f
  have hbasic : H.toScheme.basicOpen fH = H.ι ⁻¹ᵁ G.objects.left.basicOpen f :=
    (Scheme.preimage_basicOpen_top H.ι f).symm
  have hcomp : j ≫ H.ι = O.ι := G.objects.left.homOfLE_ι (invariantCore_le G H)
  apply isAffine_of_isImmersion_of_basicOpen_section j fH
  · rw [hbasic, ← Scheme.Hom.comp_preimage, hcomp]
    apply (O.ι.isAffineOpen_iff_of_isOpenImmersion).mp
    rw [O.ι.image_preimage_eq_opensRange_inf]
    simpa [inf_comm] using isAffineOpen_inf_invariantCore_of_norm G _ hf N h
  · have heq : Set.range j ∩ (H.toScheme.basicOpen fH : Set H.toScheme)ᶜ =
        (H.toScheme.basicOpen fH : Set H.toScheme)ᶜ := by
      apply Set.inter_eq_right.mpr
      intro y hy
      have hyf : y.1 ∉ G.objects.left.basicOpen f := by rwa [hbasic] at hy
      have hyo : y.1 ∈ O := (mem_invariantCore_iff G H _).2 fun r hr =>
        hres r (hr ▸ y.2) (by rwa [hr])
      exact ⟨⟨y.1, hyo⟩, Subtype.ext (congrArg (fun k => k ⟨y.1, hyo⟩) hcomp)⟩
    rw [heq]
    exact (H.toScheme.basicOpen fH).isOpen.isClosed_compl

end AlgebraicGeometry.GroupoidScheme

end
