module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.ImageClosure
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Evaluation
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct

/-!
# The reduced closure of the image of a morphism of groupoid schemes over a perfect field

Let `F : G₁ ⟶ G₂` be a morphism of groupoid schemes over a base scheme `S` which is the
identity on a common scheme of objects, and suppose that scheme of objects is the spectrum of a
perfect field. The closure of the image of `F` on arrows, with its reduced induced closed
subscheme structure, is then the arrow scheme of a groupoid scheme over `S` on the same objects,
and the closed immersion into the arrow scheme of `G₂` is a morphism of groupoid schemes.

The three structure maps lift to the reduced closure because a morphism out of a reduced scheme
factors through a reduced closed subscheme as soon as its image lies in the support
(Stacks 0356): the identity section and the inverse map the closure of the image into itself,
and for composition the source of the lift is the fibre product of two copies of the reduced
closure over the spectrum of the field, which is reduced because over a perfect field the fibre
product of two reduced schemes is reduced (Stacks 035Z).

## Main definitions

* `AlgebraicGeometry.reducedClosureArrowImage` is the vanishing ideal sheaf of the closure of
  the image on arrows, so that its closed subscheme is the reduced induced structure on that
  closure. `AlgebraicGeometry.reducedClosureArrows` is that subscheme as a scheme over the
  base, and `AlgebraicGeometry.reducedClosureArrowsι`,
  `AlgebraicGeometry.reducedClosureSource`, `AlgebraicGeometry.reducedClosureTarget` and
  `AlgebraicGeometry.reducedClosureComposable` are the morphisms it carries.
* `AlgebraicGeometry.GroupoidScheme.ReducedClosureImage` records a groupoid structure on the
  reduced closure together with its morphism to the target and the identifications of the
  components of both; `AlgebraicGeometry.GroupoidScheme.reducedClosureImage` constructs it, and
  `AlgebraicGeometry.GroupoidScheme.reducedClosureGroupoid` and
  `AlgebraicGeometry.GroupoidScheme.reducedClosureInclusion` are the groupoid and the morphism
  it carries.

## Main results

* `Stacks.Groupoids.GroupoidScheme.Hom.map_inverse`: a morphism of groupoid schemes commutes
  with the inverse maps.
* `AlgebraicGeometry.GroupoidScheme.exists_identity_lift_to_reducedClosure`,
  `AlgebraicGeometry.GroupoidScheme.exists_inverse_lift_to_reducedClosure` and
  `AlgebraicGeometry.GroupoidScheme.exists_comp_lift_to_reducedClosure`: the three structure
  maps of `G₂` lift to the reduced closure of the image.
* `AlgebraicGeometry.GroupoidScheme.reducedClosureGroupoid_objects`,
  `AlgebraicGeometry.GroupoidScheme.reducedClosureGroupoid_arrows`,
  `AlgebraicGeometry.GroupoidScheme.reducedClosureInclusion_mapObjects` and
  `AlgebraicGeometry.GroupoidScheme.reducedClosureInclusion_mapArrows_left` identify the
  components of the construction.

## Implementation notes

The groupoid axioms for the construction are checked after composing with the closed immersion
into `G₂`, which is a monomorphism, so each of them is the corresponding axiom of `G₂`. The
functoriality of the inclusion is the compatibility of the lifts with the structure maps, read
through that same monomorphism.

The construction is packaged as a structure with the identifications as fields, in the same way
as `AlgebraicGeometry.GroupoidScheme.Restriction`, because the groupoid itself is only specified
up to those identifications.

## References

* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
* [Stacks Project, Tag 04Q7](https://stacks.math.columbia.edu/tag/04Q7)
* [Stacks Project, Tag 04Q8](https://stacks.math.columbia.edu/tag/04Q8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open TopologicalSpace

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}}

/-- Composition of generalized arrows does not depend on the composability witness, so it is
compatible with replacing the first arrow by an equal one. -/
theorem compose_congr_left (G : GroupoidScheme S) {T : Over S} {f f' g : T ⟶ G.arrows}
    (h : f = f') (w : f ≫ G.source = g ≫ G.target)
    (w' : f' ≫ G.source = g ≫ G.target) : G.compose f g w = G.compose f' g w' := by
  cases h
  rfl

/-- Composition of generalized arrows does not depend on the composability witness, so it is
compatible with replacing the second arrow by an equal one. -/
theorem compose_congr_right (G : GroupoidScheme S) {T : Over S} {f g g' : T ⟶ G.arrows}
    (h : g = g') (w : f ≫ G.source = g ≫ G.target)
    (w' : f ≫ G.source = g' ≫ G.target) : G.compose f g w = G.compose f g' w' := by
  cases h
  rfl

/-- A morphism of groupoid schemes commutes with the inverse maps: on generalized points it is
a functor between groupoids, and a functor preserves inverses. -/
theorem Hom.map_inverse {G H : GroupoidScheme S} (F : Hom G H) :
    F.mapArrows ≫ H.inverse = G.inverse ≫ F.mapArrows := by
  let x : G.Evaluation G.arrows := G.source
  let y : G.Evaluation G.arrows := G.target
  let f : x ⟶ y := ⟨𝟙 G.arrows, rfl, rfl⟩
  have hi : (F.evaluation G.arrows).map (Groupoid.inv f) =
      Groupoid.inv ((F.evaluation G.arrows).map f) := by simp
  have heq : (𝟙 G.arrows ≫ G.inverse) ≫ F.mapArrows =
      (𝟙 G.arrows ≫ F.mapArrows) ≫ H.inverse := congrArg (fun z => z.arrow) hi
  simpa using heq.symm

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry

/-! ### The reduced closure of the image on arrows -/

variable {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}

/-- The vanishing ideal sheaf of the closure of the image on arrows of a morphism of groupoid
schemes: its closed subscheme is the reduced induced structure on that closure. -/
noncomputable def reducedClosureArrowImage (F : GroupoidScheme.Hom G₁ G₂) :
    G₂.arrows.left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range F.mapArrows.left.base))

/-- The closed subscheme cut out by `AlgebraicGeometry.reducedClosureArrowImage` is reduced: it
is the reduced induced structure on the closure of the image on arrows. -/
instance isReduced_subscheme_reducedClosureArrowImage (F : GroupoidScheme.Hom G₁ G₂) :
    IsReduced (reducedClosureArrowImage F).subscheme :=
  Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _

/-- `AlgebraicGeometry.reducedClosureArrowImage` is supported on the closure of the image. -/
theorem support_reducedClosureArrowImage (F : GroupoidScheme.Hom G₁ G₂) :
    ((reducedClosureArrowImage F).support : Set G₂.arrows.left) =
      closure (Set.range F.mapArrows.left.base) :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- The closed immersion of `AlgebraicGeometry.reducedClosureArrowImage` has image the closure
of the image on arrows. -/
theorem range_subschemeι_reducedClosureArrowImage (F : GroupoidScheme.Hom G₁ G₂) :
    Set.range (reducedClosureArrowImage F).subschemeι =
      closure (Set.range F.mapArrows.left.base) :=
  Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _

/-- The reduced closure of the image on arrows, as a scheme over the base. -/
noncomputable def reducedClosureArrows (F : GroupoidScheme.Hom G₁ G₂) : Over S :=
  Over.mk ((reducedClosureArrowImage F).subschemeι ≫ G₂.arrows.hom)

/-- The reduced closure of the image on arrows is a reduced scheme. -/
instance isReduced_reducedClosureArrows (F : GroupoidScheme.Hom G₁ G₂) :
    IsReduced (reducedClosureArrows F).left :=
  isReduced_subscheme_reducedClosureArrowImage F

/-- The closed immersion of the reduced closure of the image into the arrow scheme of the
target, as a morphism of schemes over the base. -/
noncomputable def reducedClosureArrowsι (F : GroupoidScheme.Hom G₁ G₂) :
    reducedClosureArrows F ⟶ G₂.arrows :=
  Over.homMk (reducedClosureArrowImage F).subschemeι rfl

/-- The closed immersion of the reduced closure of the image is a monomorphism of schemes over
the base. -/
instance mono_reducedClosureArrowsι (F : GroupoidScheme.Hom G₁ G₂) :
    Mono (reducedClosureArrowsι F) :=
  have : Mono (reducedClosureArrowsι F).left :=
    (inferInstance : Mono (reducedClosureArrowImage F).subschemeι)
  Over.mono_of_mono_left _

/-- The source map of the target groupoid restricted to the reduced closure of the image. -/
noncomputable def reducedClosureSource (F : GroupoidScheme.Hom G₁ G₂) :
    reducedClosureArrows F ⟶ G₂.objects :=
  reducedClosureArrowsι F ≫ G₂.source

/-- The target map of the target groupoid restricted to the reduced closure of the image. -/
noncomputable def reducedClosureTarget (F : GroupoidScheme.Hom G₁ G₂) :
    reducedClosureArrows F ⟶ G₂.objects :=
  reducedClosureArrowsι F ≫ G₂.target

/-- The morphism from the composable pairs of arrows of the reduced closure of the image to the
composable pairs of arrows of the target groupoid. -/
noncomputable def reducedClosureComposable (F : GroupoidScheme.Hom G₁ G₂) :
    pullback (reducedClosureSource F) (reducedClosureTarget F) ⟶
      pullback G₂.source G₂.target :=
  pullback.map _ _ G₂.source G₂.target (reducedClosureArrowsι F) (reducedClosureArrowsι F)
    (𝟙 G₂.objects) (by simp [reducedClosureSource]) (by simp [reducedClosureTarget])

namespace GroupoidScheme

/-! ### Lifting the structure maps to the reduced closure -/

/-- A morphism over the base into the arrow scheme of the target whose image lies in the closure
of the image on arrows factors through the reduced closure of that image, provided its source is
reduced. -/
theorem exists_lift_to_reducedClosureArrows (F : GroupoidScheme.Hom G₁ G₂) {T : Over S}
    [IsReduced T.left] (f : T ⟶ G₂.arrows)
    (hf : Set.range f.left.base ⊆ closure (Set.range F.mapArrows.left.base)) :
    ∃ e : T ⟶ reducedClosureArrows F, e ≫ reducedClosureArrowsι F = f := by
  obtain ⟨e, he⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    (reducedClosureArrowImage F) f.left).mpr
      (by rw [support_reducedClosureArrowImage]; exact hf)
  refine ⟨Over.homMk e ?_, Over.OverMorphism.ext he⟩
  show e ≫ (reducedClosureArrowImage F).subschemeι ≫ G₂.arrows.hom = T.hom
  rw [← Category.assoc, he, Over.w]

/-- The identity section of the target groupoid lands in the image on arrows, because the
morphism is the identity on objects and carries identities to identities. -/
private theorem range_identity_subset_closure_range_mapArrows (F : GroupoidScheme.Hom G₁ G₂)
    (hobjects : G₁.objects = G₂.objects) (hmapObjects : F.mapObjects = eqToHom hobjects) :
    Set.range G₂.identity.left.base ⊆ closure (Set.range F.mapArrows.left.base) := by
  rintro y ⟨x, rfl⟩
  have ho : G₁.objects.left = G₂.objects.left := congrArg Over.left hobjects
  have hmap : F.mapObjects.left = eqToHom ho := by
    simpa using congrArg Over.Hom.left hmapObjects
  have hid : F.mapObjects.left ≫ G₂.identity.left =
      G₁.identity.left ≫ F.mapArrows.left := by
    simpa using congrArg Over.Hom.left F.map_identity
  refine subset_closure ⟨G₁.identity.left.base ((eqToHom ho.symm).base x), ?_⟩
  have hx : F.mapObjects.left.base ((eqToHom ho.symm).base x) = x := by
    rw [hmap]
    exact congrArg (fun f : G₂.objects.left ⟶ G₂.objects.left => f.base x)
      (eqToHom_trans ho.symm ho)
  have heq := congrArg (fun f : G₁.objects.left ⟶ G₂.arrows.left =>
    f.base ((eqToHom ho.symm).base x)) hid
  change G₂.identity.left.base (F.mapObjects.left.base ((eqToHom ho.symm).base x)) =
    F.mapArrows.left.base (G₁.identity.left.base ((eqToHom ho.symm).base x)) at heq
  rw [← heq, hx]

/-- The identity section of the target groupoid factors through the reduced closure of the
image on arrows. -/
theorem exists_identity_lift_to_reducedClosure {k : Type u} [Field k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    ∃ e : G₂.objects ⟶ reducedClosureArrows F,
      e ≫ reducedClosureArrowsι F = G₂.identity := by
  have hfield₂ : G₂.objects.left = Spec (.of k) :=
    (congrArg Over.left hobjects.symm).trans hfield
  have : IsReduced G₂.objects.left :=
    hfield₂ ▸ (inferInstance : IsReduced (Spec (CommRingCat.of k)))
  exact exists_lift_to_reducedClosureArrows F G₂.identity
    (range_identity_subset_closure_range_mapArrows F hobjects hmapObjects)

/-- The inverse of the target groupoid maps the closure of the image on arrows into itself. -/
private theorem mapsTo_inverse_closure_range_mapArrows (F : GroupoidScheme.Hom G₁ G₂) :
    Set.MapsTo G₂.inverse.left.base (closure (Set.range F.mapArrows.left.base))
      (closure (Set.range F.mapArrows.left.base)) := by
  refine Set.MapsTo.closure (s := Set.range F.mapArrows.left.base) ?_
    G₂.inverse.left.continuous
  rintro y ⟨x, rfl⟩
  exact ⟨G₁.inverse.left.base x, (congrArg
    (fun f : G₁.arrows.left ⟶ G₂.arrows.left => f.base x)
    (congrArg Over.Hom.left F.map_inverse)).symm⟩

/-- The inverse of the target groupoid, restricted to the reduced closure of the image on
arrows, factors through that reduced closure. -/
theorem exists_inverse_lift_to_reducedClosure (F : GroupoidScheme.Hom G₁ G₂) :
    ∃ e : reducedClosureArrows F ⟶ reducedClosureArrows F,
      e ≫ reducedClosureArrowsι F = reducedClosureArrowsι F ≫ G₂.inverse :=
  exists_lift_to_reducedClosureArrows F (reducedClosureArrowsι F ≫ G₂.inverse) (by
    rintro y ⟨x, rfl⟩
    exact mapsTo_inverse_closure_range_mapArrows F
      ((range_subschemeι_reducedClosureArrowImage F) ▸ Set.mem_range_self x))

/-- A fibre product in the over category over an object whose underlying scheme is the spectrum
of a perfect field, of two reduced schemes, is reduced. -/
@[sga "3 VIA 0.2" "Binary products"]
private theorem isReduced_overPullback_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z) (hZ : Z.left = Spec (.of k))
    [IsReduced X.left] [IsReduced Y.left] : IsReduced (pullback f g).left := by
  have hred : IsReduced (pullback (f.left ≫ eqToHom hZ) (g.left ≫ eqToHom hZ)) :=
    isReduced_pullback_over_perfectField _ _
  exact ObjectProperty.prop_of_iso IsReduced
    (((overFibreProduct_isPullback f g).comp_isIso (eqToHom hZ)).isoPullback).symm hred

/-- The first projection of the composable pairs commutes with the inclusion of the reduced
closure. -/
private theorem reducedClosureComposable_fst (F : GroupoidScheme.Hom G₁ G₂) :
    reducedClosureComposable F ≫ pullback.fst G₂.source G₂.target =
      pullback.fst (reducedClosureSource F) (reducedClosureTarget F) ≫
        reducedClosureArrowsι F := pullback.lift_fst _ _ _

/-- The second projection of the composable pairs commutes with the inclusion of the reduced
closure. -/
private theorem reducedClosureComposable_snd (F : GroupoidScheme.Hom G₁ G₂) :
    reducedClosureComposable F ≫ pullback.snd G₂.source G₂.target =
      pullback.snd (reducedClosureSource F) (reducedClosureTarget F) ≫
        reducedClosureArrowsι F := pullback.lift_snd _ _ _

/-- Composition in the target groupoid, restricted to the pairs of composable arrows lying in
the reduced closure of the image on arrows, factors through that reduced closure. -/
theorem exists_comp_lift_to_reducedClosure {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    ∃ e : pullback (reducedClosureSource F) (reducedClosureTarget F) ⟶ reducedClosureArrows F,
      e ≫ reducedClosureArrowsι F = reducedClosureComposable F ≫ G₂.comp := by
  have hfield₂ : G₂.objects.left = Spec (.of k) :=
    (congrArg Over.left hobjects.symm).trans hfield
  have : IsReduced (pullback (reducedClosureSource F) (reducedClosureTarget F)).left :=
    isReduced_overPullback_of_perfectField _ _ hfield₂
  have hmem {T : Over S} (m : T ⟶ reducedClosureArrows F) (p : T.left) :
      (m ≫ reducedClosureArrowsι F).left.base p ∈ closure (Set.range F.mapArrows.left.base) := by
    rw [← range_subschemeι_reducedClosureArrowImage F]
    exact ⟨m.left.base p, rfl⟩
  refine exists_lift_to_reducedClosureArrows F (reducedClosureComposable F ≫ G₂.comp) ?_
  rintro z ⟨p, rfl⟩
  refine comp_mapsTo_closure_range_mapArrows (k := k) F hobjects hfield hmapObjects ⟨?_, ?_⟩
  · have := hmem (pullback.fst _ _) p
    rwa [← reducedClosureComposable_fst F] at this
  · have := hmem (pullback.snd _ _) p
    rwa [← reducedClosureComposable_snd F] at this

/-! ### The groupoid structure on the reduced closure -/

/-- A groupoid structure on the reduced closure of the image on arrows of a morphism of groupoid
schemes, together with the closed immersion into the target as a morphism of groupoid schemes
and the identifications of the components of both. -/
structure ReducedClosureImage (F : GroupoidScheme.Hom G₁ G₂) where
  /-- The groupoid scheme carried by the reduced closure of the image. -/
  groupoid : GroupoidScheme S
  /-- Its scheme of objects is that of the target. -/
  objects_eq : groupoid.objects = G₂.objects
  /-- Its scheme of arrows is the reduced closure of the image. -/
  arrows_eq : groupoid.arrows = reducedClosureArrows F
  /-- The canonical morphism to the target groupoid. -/
  hom : GroupoidScheme.Hom groupoid G₂
  /-- Its map on objects is the identity. -/
  mapObjects_eq : hom.mapObjects = eqToHom objects_eq
  /-- Its map on arrows is the closed immersion of the reduced closure. -/
  mapArrows_eq : hom.mapArrows = eqToHom arrows_eq ≫ reducedClosureArrowsι F

/-- The reduced closure of the image on arrows of a morphism of groupoid schemes over a perfect
field which is the identity on objects admits a groupoid structure for which the closed
immersion into the target is a morphism of groupoid schemes. -/
@[sga "3 VIA 0.2" "special case"]
theorem nonempty_reducedClosureImage {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) : Nonempty (ReducedClosureImage F) := by
  obtain ⟨idH, hIdI⟩ :=
    exists_identity_lift_to_reducedClosure (k := k) F hobjects hfield hmapObjects
  obtain ⟨invH, hInvI⟩ := exists_inverse_lift_to_reducedClosure F
  obtain ⟨compH, hCompI⟩ :=
    exists_comp_lift_to_reducedClosure (k := k) F hobjects hfield hmapObjects
  have hS : reducedClosureSource F = reducedClosureArrowsι F ≫ G₂.source := rfl
  have hT : reducedClosureTarget F = reducedClosureArrowsι F ≫ G₂.target := rfl
  have hcompose {T : Over S} (a b : T ⟶ reducedClosureArrows F) {x y : T ⟶ G₂.arrows}
      (ha : a ≫ reducedClosureArrowsι F = x) (hb : b ≫ reducedClosureArrowsι F = y)
      (w : a ≫ reducedClosureSource F = b ≫ reducedClosureTarget F)
      (w' : x ≫ G₂.source = y ≫ G₂.target) :
      (pullback.lift a b w ≫ compH) ≫ reducedClosureArrowsι F = G₂.compose x y w' := by
    subst ha hb
    have hfac : pullback.lift a b w ≫ reducedClosureComposable F =
        pullback.lift (a ≫ reducedClosureArrowsι F) (b ≫ reducedClosureArrowsι F) w' := by
      apply pullback.hom_ext
      · rw [Category.assoc, reducedClosureComposable_fst F, ← Category.assoc, pullback.lift_fst,
          pullback.lift_fst]
      · rw [Category.assoc, reducedClosureComposable_snd F, ← Category.assoc, pullback.lift_snd,
          pullback.lift_snd]
    rw [Category.assoc, hCompI, ← Category.assoc, hfac]
    rfl
  have hidArrow : ∀ {T : Over S} (f : T ⟶ reducedClosureArrows F),
      (f ≫ reducedClosureSource F ≫ idH) ≫ reducedClosureArrowsι F =
        (f ≫ reducedClosureArrowsι F) ≫ G₂.source ≫ G₂.identity := by
    intro T f
    rw [hS]
    simp only [Category.assoc, hIdI]
  have htgtArrow : ∀ {T : Over S} (f : T ⟶ reducedClosureArrows F),
      (f ≫ reducedClosureTarget F ≫ idH) ≫ reducedClosureArrowsι F =
        (f ≫ reducedClosureArrowsι F) ≫ G₂.target ≫ G₂.identity := by
    intro T f
    rw [hT]
    simp only [Category.assoc, hIdI]
  have hinvArrow : ∀ {T : Over S} (f : T ⟶ reducedClosureArrows F),
      (f ≫ invH) ≫ reducedClosureArrowsι F =
        (f ≫ reducedClosureArrowsι F) ≫ G₂.inverse := by
    intro T f
    simp only [Category.assoc, hInvI]
  refine ⟨
    { groupoid :=
        { objects := G₂.objects
          arrows := reducedClosureArrows F
          source := reducedClosureSource F
          target := reducedClosureTarget F
          comp := compH
          identity := idH
          inverse := invH
          source_identity := by
            rw [hS, ← Category.assoc, hIdI, G₂.source_identity]
          target_identity := by
            rw [hT, ← Category.assoc, hIdI, G₂.target_identity]
          source_inverse := by
            rw [hS, hT, ← Category.assoc, hInvI, Category.assoc, G₂.source_inverse]
          target_inverse := by
            rw [hT, hS, ← Category.assoc, hInvI, Category.assoc, G₂.target_inverse]
          source_comp := by
            show compH ≫ reducedClosureArrowsι F ≫ G₂.source =
              pullback.snd (reducedClosureSource F) (reducedClosureTarget F) ≫
                reducedClosureArrowsι F ≫ G₂.source
            rw [← Category.assoc, hCompI, Category.assoc, G₂.source_comp, ← Category.assoc,
              reducedClosureComposable_snd F, Category.assoc]
          target_comp := by
            show compH ≫ reducedClosureArrowsι F ≫ G₂.target =
              pullback.fst (reducedClosureSource F) (reducedClosureTarget F) ≫
                reducedClosureArrowsι F ≫ G₂.target
            rw [← Category.assoc, hCompI, Category.assoc, G₂.target_comp, ← Category.assoc,
              reducedClosureComposable_fst F, Category.assoc]
          left_identity := fun T f w => by
            refine (cancel_mono (reducedClosureArrowsι F)).1 ?_
            have w₀ : ((f ≫ reducedClosureArrowsι F) ≫ G₂.target ≫ G₂.identity) ≫
                G₂.source = (f ≫ reducedClosureArrowsι F) ≫ G₂.target := by
              simp only [Category.assoc, G₂.source_identity, Category.comp_id]
            rw [hcompose (f ≫ reducedClosureTarget F ≫ idH) f (htgtArrow f) rfl w w₀]
            exact G₂.left_identity T (f ≫ reducedClosureArrowsι F) w₀
          right_identity := fun T f w => by
            refine (cancel_mono (reducedClosureArrowsι F)).1 ?_
            have w₀ : (f ≫ reducedClosureArrowsι F) ≫ G₂.source =
                ((f ≫ reducedClosureArrowsι F) ≫ G₂.source ≫ G₂.identity) ≫
                  G₂.target := by
              simp only [Category.assoc, G₂.target_identity, Category.comp_id]
            rw [hcompose f (f ≫ reducedClosureSource F ≫ idH) rfl (hidArrow f) w w₀]
            exact G₂.right_identity T (f ≫ reducedClosureArrowsι F) w₀
          left_inverse := fun T f w => by
            refine (cancel_mono (reducedClosureArrowsι F)).1 ?_
            have w₀ : ((f ≫ reducedClosureArrowsι F) ≫ G₂.inverse) ≫ G₂.source =
                (f ≫ reducedClosureArrowsι F) ≫ G₂.target := by
              simp only [Category.assoc, G₂.source_inverse]
            rw [hcompose (f ≫ invH) f (hinvArrow f) rfl w w₀]
            exact (G₂.left_inverse T (f ≫ reducedClosureArrowsι F) w₀).trans
              (hidArrow f).symm
          right_inverse := fun T f w => by
            refine (cancel_mono (reducedClosureArrowsι F)).1 ?_
            have w₀ : (f ≫ reducedClosureArrowsι F) ≫ G₂.source =
                ((f ≫ reducedClosureArrowsι F) ≫ G₂.inverse) ≫ G₂.target := by
              simp only [Category.assoc, G₂.target_inverse]
            rw [hcompose f (f ≫ invH) rfl (hinvArrow f) w w₀]
            exact (G₂.right_inverse T (f ≫ reducedClosureArrowsι F) w₀).trans
              (htgtArrow f).symm
          assoc := fun T f g h wfg wgh w₁ w₂ => by
            refine (cancel_mono (reducedClosureArrowsι F)).1 ?_
            have wfg' : (f ≫ reducedClosureArrowsι F) ≫ G₂.source =
                (g ≫ reducedClosureArrowsι F) ≫ G₂.target := by
              simpa only [Category.assoc, ← hS, ← hT] using wfg
            have wgh' : (g ≫ reducedClosureArrowsι F) ≫ G₂.source =
                (h ≫ reducedClosureArrowsι F) ≫ G₂.target := by
              simpa only [Category.assoc, ← hS, ← hT] using wgh
            have hfg := hcompose f g rfl rfl wfg wfg'
            have hgh := hcompose g h rfl rfl wgh wgh'
            have w₁' : G₂.compose (f ≫ reducedClosureArrowsι F)
                (g ≫ reducedClosureArrowsι F) wfg' ≫ G₂.source =
                (h ≫ reducedClosureArrowsι F) ≫ G₂.target := by
              rw [← hfg]; simpa only [Category.assoc, ← hS, ← hT] using w₁
            have w₂' : (f ≫ reducedClosureArrowsι F) ≫ G₂.source =
                G₂.compose (g ≫ reducedClosureArrowsι F)
                  (h ≫ reducedClosureArrowsι F) wgh' ≫ G₂.target := by
              rw [← hgh]; simpa only [Category.assoc, ← hS, ← hT] using w₂
            rw [hcompose _ h hfg rfl w₁ w₁', hcompose f _ rfl hgh w₂ w₂']
            exact G₂.assoc T (f ≫ reducedClosureArrowsι F) (g ≫ reducedClosureArrowsι F)
              (h ≫ reducedClosureArrowsι F) wfg' wgh' w₁' w₂' }
      objects_eq := rfl
      arrows_eq := rfl
      hom :=
        { mapObjects := 𝟙 G₂.objects
          mapArrows := reducedClosureArrowsι F
          map_source := (Category.comp_id (reducedClosureSource F)).symm
          map_target := (Category.comp_id (reducedClosureTarget F)).symm
          map_identity := by rw [Category.id_comp]; exact hIdI.symm
          map_comp := fun T f g w w' => hcompose f g rfl rfl w w' }
      mapObjects_eq := rfl
      mapArrows_eq := by simp only [eqToHom_refl, Category.id_comp] }⟩

/-- **Stacks Project, Tag 04Q8.** The reduced closure of the image on arrows of a morphism of
groupoid schemes over a perfect field which is the identity on objects carries a groupoid
structure for which the closed immersion into the target is a morphism of groupoid schemes. -/
@[stacks 04Q8 "construction", sga "3 VIA 0.2" "special case"]
noncomputable def reducedClosureImage {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) : ReducedClosureImage F :=
  Classical.choice (nonempty_reducedClosureImage F hobjects hfield hmapObjects)

/-- The groupoid scheme whose arrows are the reduced closure of the image on arrows. -/
noncomputable def reducedClosureGroupoid {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) : GroupoidScheme S :=
  (reducedClosureImage F hobjects hfield hmapObjects).groupoid

/-- The canonical morphism from the reduced-closure groupoid to the target groupoid. -/
noncomputable def reducedClosureInclusion {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    GroupoidScheme.Hom (reducedClosureGroupoid F hobjects hfield hmapObjects) G₂ :=
  (reducedClosureImage F hobjects hfield hmapObjects).hom

/-- **Stacks Project, Tag 04Q8.** The reduced-closure groupoid has the same scheme of objects
as the target groupoid. -/
@[stacks 04Q8 "object scheme"]
theorem reducedClosureGroupoid_objects {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    (reducedClosureGroupoid F hobjects hfield hmapObjects).objects = G₂.objects :=
  (reducedClosureImage F hobjects hfield hmapObjects).objects_eq

/-- **Stacks Project, Tag 04Q8.** The scheme of arrows of the reduced-closure groupoid is the
reduced closure of the image on arrows. -/
@[stacks 04Q8 "arrow scheme"]
theorem reducedClosureGroupoid_arrows {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    (reducedClosureGroupoid F hobjects hfield hmapObjects).arrows = reducedClosureArrows F :=
  (reducedClosureImage F hobjects hfield hmapObjects).arrows_eq

/-- **Stacks Project, Tag 04Q8.** The canonical morphism from the reduced-closure groupoid is
the identity on objects. -/
@[stacks 04Q8 "inclusion on objects"]
theorem reducedClosureInclusion_mapObjects {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    (reducedClosureInclusion F hobjects hfield hmapObjects).mapObjects =
      eqToHom (reducedClosureGroupoid_objects F hobjects hfield hmapObjects) :=
  (reducedClosureImage F hobjects hfield hmapObjects).mapObjects_eq

/-- The canonical morphism from the reduced-closure groupoid is, on arrows, the closed
immersion of the reduced closure of the image. -/
theorem reducedClosureInclusion_mapArrows {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    (reducedClosureInclusion F hobjects hfield hmapObjects).mapArrows =
      eqToHom (reducedClosureGroupoid_arrows F hobjects hfield hmapObjects) ≫
        reducedClosureArrowsι F :=
  (reducedClosureImage F hobjects hfield hmapObjects).mapArrows_eq

/-- **Stacks Project, Tag 04Q8.** On arrows the canonical morphism from the reduced-closure
groupoid is the closed immersion of the reduced closure of the image. -/
@[stacks 04Q8 "inclusion on arrows"]
theorem reducedClosureInclusion_mapArrows_left {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    (reducedClosureInclusion F hobjects hfield hmapObjects).mapArrows.left =
      eqToHom (congrArg Over.left
        (reducedClosureGroupoid_arrows F hobjects hfield hmapObjects)) ≫
        (reducedClosureArrowImage F).subschemeι := by
  rw [reducedClosureInclusion_mapArrows, Over.comp_left, Over.eqToHom_left]
  rfl

end GroupoidScheme

end AlgebraicGeometry

end
