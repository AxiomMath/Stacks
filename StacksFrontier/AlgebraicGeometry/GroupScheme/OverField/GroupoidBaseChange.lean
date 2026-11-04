module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback

/-!
# Base change of a groupoid scheme

A groupoid scheme can be pulled back along an arbitrary morphism of base schemes.  The
projections of the two pulled-back schemes are compatible with all the groupoid structure maps.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.HomOver` is a morphism of groupoid schemes lying over a
  morphism of their base schemes.
* `AlgebraicGeometry.GroupoidScheme.BaseChange` packages a groupoid scheme together with a
  cartesian projection to the original groupoid scheme.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_baseChange` constructs the base change of a groupoid
  scheme.

## Implementation notes

The source describes the projection as a morphism of groupoid schemes over the original base.
Here it is recorded equivalently as a morphism over the given map of bases.  Its object and
arrow squares are required to be cartesian; compatibility with source, target, identity and
composition then says precisely that all the structure maps are their base changes.

## References

* [Stacks Project, Tag 0DT8](https://stacks.math.columbia.edu/tag/0DT8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

namespace AlgebraicGeometry.GroupoidScheme

universe u

/-- A morphism of groupoid schemes whose map on bases is `f`.

The functor `Over.map f` regards an object over `S'` as an object over `S`, so the two
displayed maps are morphisms in the same over category as the structure maps of `G`. -/
structure HomOver {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G' : Stacks.Groupoids.GroupoidScheme S') (G : Stacks.Groupoids.GroupoidScheme S) where
  /-- The map on objects. -/
  mapObjects : (Over.map f).obj G'.objects ⟶ G.objects
  /-- The map on arrows. -/
  mapArrows : (Over.map f).obj G'.arrows ⟶ G.arrows
  map_source : mapArrows ≫ G.source = (Over.map f).map G'.source ≫ mapObjects
  map_target : mapArrows ≫ G.target = (Over.map f).map G'.target ≫ mapObjects
  map_identity : mapObjects ≫ G.identity = (Over.map f).map G'.identity ≫ mapArrows
  map_comp : ∀ (T : Over S') (a b : T ⟶ G'.arrows)
      (w : a ≫ G'.source = b ≫ G'.target)
      (w' : ((Over.map f).map a ≫ mapArrows) ≫ G.source =
        ((Over.map f).map b ≫ mapArrows) ≫ G.target),
    (Over.map f).map (G'.compose a b w) ≫ mapArrows =
      G.compose ((Over.map f).map a ≫ mapArrows)
        ((Over.map f).map b ≫ mapArrows) w'

/-- A base change of `G` along `f`, including its canonical projection.

The last two fields assert that its object and arrow schemes are the fibre products with
`S'`. -/
structure BaseChange {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : Stacks.Groupoids.GroupoidScheme S) where
  /-- The groupoid scheme over the new base. -/
  groupoid : Stacks.Groupoids.GroupoidScheme S'
  /-- The projection to the original groupoid scheme. -/
  projection : HomOver f groupoid G
  isPullback_objects : IsPullback projection.mapObjects.left groupoid.objects.hom G.objects.hom f
  isPullback_arrows : IsPullback projection.mapArrows.left groupoid.arrows.hom G.arrows.hom f

/-- Base-changing the object and arrow schemes of a groupoid scheme, and all its structure
maps, produces a groupoid scheme over the new base whose projections form a morphism of
groupoid schemes. -/
@[stacks 0DT8]
theorem exists_baseChange {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : Stacks.Groupoids.GroupoidScheme S) : Nonempty (BaseChange f G) := by
  classical
  let F : CategoryTheory.Functor (Over S) (Over S') := Over.pullback f
  let e (a b : G.arrows ⟶ G.objects) :
      pullback (F.map a) (F.map b) ≅ F.obj (pullback a b) :=
    (PreservesPullback.iso F a b).symm
  have map_map {X Y : Over S} (T : Over S') (a : T ⟶ F.obj X) (g : X ⟶ Y) :
      (Over.map f).map (a ≫ F.map g) ≫ (Over.mapPullbackAdj f).counit.app Y =
        (Over.map f).map a ≫ (Over.mapPullbackAdj f).counit.app X ≫ g := by
    simpa only [Functor.map_comp, Functor.comp_map, Category.assoc, Functor.id_map] using congrArg
      (fun z ↦ (Over.map f).map a ≫ z) ((Over.mapPullbackAdj f).counit.naturality g)
  have map_map_two {X Y Z : Over S} (T : Over S') (a : T ⟶ F.obj X)
      (g : X ⟶ Y) (h : Y ⟶ Z) :
      (Over.map f).map (a ≫ F.map g ≫ F.map h) ≫
          (Over.mapPullbackAdj f).counit.app Z =
        ((Over.map f).map a ≫ (Over.mapPullbackAdj f).counit.app X) ≫ g ≫ h := by
    simpa only [F.map_comp, Category.assoc] using map_map T a (g ≫ h)
  have map_rel {X Y : Over S} (T : Over S') (a b : T ⟶ F.obj X)
      (g h : X ⟶ Y) (w : a ≫ F.map g = b ≫ F.map h) :
      ((Over.map f).map a ≫ (Over.mapPullbackAdj f).counit.app X) ≫ g =
        ((Over.map f).map b ≫ (Over.mapPullbackAdj f).counit.app X) ≫ h := by
    simpa only [map_map T a g, map_map T b h, Category.assoc, Functor.id_obj] using
      congrArg (fun z ↦ (Over.map f).map z ≫ (Over.mapPullbackAdj f).counit.app Y) w
  have hinj {T : Over S'} {x y : T ⟶ F.obj G.arrows}
      (h : (Over.map f).map x ≫ (Over.mapPullbackAdj f).counit.app G.arrows =
        (Over.map f).map y ≫ (Over.mapPullbackAdj f).counit.app G.arrows) : x = y :=
    ((Over.mapPullbackAdj f).homEquiv T G.arrows).symm.injective
      (by simpa only [Adjunction.homEquiv_counit] using h)
  have map_comp_base (T : Over S') (a b : T ⟶ F.obj G.arrows)
      (w : a ≫ F.map G.source = b ≫ F.map G.target) :
      (Over.map f).map
          (pullback.lift a b w ≫ (e G.source G.target).hom ≫ F.map G.comp) ≫
          (Over.mapPullbackAdj f).counit.app G.arrows =
        pullback.lift
            ((Over.map f).map a ≫ (Over.mapPullbackAdj f).counit.app G.arrows)
            ((Over.map f).map b ≫ (Over.mapPullbackAdj f).counit.app G.arrows)
            (map_rel T a b G.source G.target w) ≫
          G.comp := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.comp_map]
    dsimp only [F]
    rw [(Over.mapPullbackAdj f).counit.naturality G.comp]
    have h :
        (Over.map f).map (pullback.lift a b w) ≫
              (Over.map f).map (e G.source G.target).hom ≫
              (Over.mapPullbackAdj f).counit.app (pullback G.source G.target) =
          pullback.lift
            ((Over.map f).map a ≫ (Over.mapPullbackAdj f).counit.app G.arrows)
            ((Over.map f).map b ≫ (Over.mapPullbackAdj f).counit.app G.arrows)
            (map_rel T a b G.source G.target w) := by
      apply pullback.hom_ext
      · have := map_map T (pullback.lift a b w ≫ (e G.source G.target).hom)
          (pullback.fst G.source G.target)
        simp only [e, Iso.symm_hom, Category.assoc, PreservesPullback.iso_inv_fst,
          pullback.lift_fst, Functor.map_comp] at this
        rw [pullback.lift_fst]
        exact this.symm
      · have := map_map T (pullback.lift a b w ≫ (e G.source G.target).hom)
          (pullback.snd G.source G.target)
        simp only [e, Iso.symm_hom, Category.assoc, PreservesPullback.iso_inv_snd,
          pullback.lift_snd, Functor.map_comp] at this
        rw [pullback.lift_snd]
        exact this.symm
    simpa only [Functor.id_map, Category.assoc] using congrArg (fun z ↦ z ≫ G.comp) h
  let G' : Stacks.Groupoids.GroupoidScheme S' :=
    { objects := F.obj G.objects
      arrows := F.obj G.arrows
      source := F.map G.source
      target := F.map G.target
      comp := (e G.source G.target).hom ≫ F.map G.comp
      identity := F.map G.identity
      inverse := F.map G.inverse
      source_identity := by
        rw [← F.map_comp, G.source_identity, F.map_id]
      target_identity := by
        rw [← F.map_comp, G.target_identity, F.map_id]
      source_inverse := by
        rw [← F.map_comp, G.source_inverse]
      target_inverse := by
        rw [← F.map_comp, G.target_inverse]
      source_comp := by
        rw [Category.assoc, ← F.map_comp, G.source_comp, F.map_comp]
        simp [e]
      target_comp := by
        rw [Category.assoc, ← F.map_comp, G.target_comp, F.map_comp]
        simp [e]
      left_identity := by
        intro T a w
        apply hinj
        rw [map_comp_base T _ _ w]
        simp only [map_map_two T a G.target G.identity]
        exact G.left_identity ((Over.map f).obj T)
          ((Over.map f).map a ≫ (Over.mapPullbackAdj f).counit.app G.arrows)
          (by simp only [Category.assoc, G.source_identity, Category.comp_id])
      right_identity := by
        intro T a w
        apply hinj
        rw [map_comp_base T _ _ w]
        simp only [map_map_two T a G.source G.identity]
        exact G.right_identity ((Over.map f).obj T)
          ((Over.map f).map a ≫ (Over.mapPullbackAdj f).counit.app G.arrows)
          (by simp only [Category.assoc, G.target_identity, Category.comp_id])
      left_inverse := by
        intro T a w
        apply hinj
        rw [map_comp_base T _ _ w]
        simp only [map_map T a G.inverse, map_map_two T a G.source G.identity]
        exact G.left_inverse ((Over.map f).obj T)
          ((Over.map f).map a ≫ (Over.mapPullbackAdj f).counit.app G.arrows)
          (by simp only [Category.assoc, G.source_inverse])
      right_inverse := by
        intro T a w
        apply hinj
        rw [map_comp_base T _ _ w]
        simp only [map_map T a G.inverse, map_map_two T a G.target G.identity]
        exact G.right_inverse ((Over.map f).obj T)
          ((Over.map f).map a ≫ (Over.mapPullbackAdj f).counit.app G.arrows)
          (by simp only [Category.assoc, G.target_inverse])
      assoc := by
        intro T a b c wab wbc w₁ w₂
        apply hinj
        rw [map_comp_base T _ c w₁, map_comp_base T a _ w₂]
        simp only [map_comp_base T a b wab, map_comp_base T b c wbc]
        rw [G.assoc] }
  let pO : (Over.map f).obj G'.objects ⟶ G.objects :=
    (Over.mapPullbackAdj f).counit.app G.objects
  let pA : (Over.map f).obj G'.arrows ⟶ G.arrows :=
    (Over.mapPullbackAdj f).counit.app G.arrows
  refine ⟨⟨G', ?_, ?_, ?_⟩⟩
  · refine
      { mapObjects := pO
        mapArrows := pA
        map_source := by simpa [pO, pA, G', F] using
          ((Over.mapPullbackAdj f).counit.naturality G.source).symm
        map_target := by simpa [pO, pA, G', F] using
          ((Over.mapPullbackAdj f).counit.naturality G.target).symm
        map_identity := by simpa [pO, pA, G', F] using
          ((Over.mapPullbackAdj f).counit.naturality G.identity).symm
        map_comp := ?_ }
    intro T a b w w'
    exact map_comp_base T a b w
  · simpa [pO, G', F] using IsPullback.of_hasPullback G.objects.hom f
  · simpa [pA, G', F] using IsPullback.of_hasPullback G.arrows.hom f

end AlgebraicGeometry.GroupoidScheme

end
