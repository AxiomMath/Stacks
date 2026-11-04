module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.ReducedClosureGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Restriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.OpenImageOverField

/-!
# Locally closed images of morphisms of groupoid schemes over a field

The image on arrows of a morphism of groupoid schemes which is the identity on a common scheme
of objects, when that scheme of objects is the spectrum of a field, is closed as soon as it is
locally closed.

Over a perfect field the argument goes through the reduced closure of the image: the identity
morphism of the source groupoid has the whole arrow scheme as reduced closure, the given
morphism induces a morphism between the two reduced closures, and the image of that induced
morphism is the preimage of the original image under a closed embedding whose image is the
closure of the original image. A locally closed subset is open in its closure, so that induced
image is open, hence closed by Stacks 04Q6, and its image under the closed embedding is the
original image.

Over an arbitrary field one first restricts both groupoids along the spectrum of the perfect
closure. That restriction does not change the underlying topological space of either arrow
scheme, because the perfect closure is a purely inseparable extension, so closedness of the
image transfers back.

## Main results

* `AlgebraicGeometry.isClosed_range_mapArrows_of_isLocallyClosed`: **Stacks 04Q9**, a locally
  closed image on arrows is closed.
* `AlgebraicGeometry.isClosed_range_mapArrows_of_isLocallyClosed_of_perfectField`: the same
  over a perfect field, which is the main step.
* `AlgebraicGeometry.exists_hom_reducedClosureGroupoid`: the morphism between the reduced
  closures of the images of the identity and of a given morphism.

## Implementation notes

That the two groupoids share their scheme of objects is expressed by an equality in the over
category, and that the map on objects is the identity by the corresponding equality morphism;
the hypothesis that the common scheme of objects is the spectrum of a field is likewise an
equality of schemes. The image is the range of the underlying continuous map on arrow schemes.

The perfect closure of `k` is `perfectClosure k (AlgebraicClosure k)`, the largest purely
inseparable subextension of an algebraic closure.

## References

* [Stacks Project, Tag 046X](https://stacks.math.columbia.edu/tag/046X)
* [Stacks Project, Tag 04Q6](https://stacks.math.columbia.edu/tag/04Q6)
* [Stacks Project, Tag 04Q9](https://stacks.math.columbia.edu/tag/04Q9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace Set

/-- In a commuting square `j₂ ∘ f' = f ∘ j₁` with `j₁` surjective and `j₂` injective, the range
of `f'` is the preimage under `j₂` of the range of `f`. -/
theorem range_eq_preimage_range_of_comm {X' X Y' Y : Type*} {f' : X' → Y'} {f : X → Y}
    {j₁ : X' → X} {j₂ : Y' → Y} (h : ∀ x, j₂ (f' x) = f (j₁ x))
    (h₁ : Function.Surjective j₁) (h₂ : Function.Injective j₂) :
    range f' = j₂ ⁻¹' range f := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, (h x).symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := h₁ x
    exact ⟨z, h₂ ((h z).trans hx)⟩

end Set

namespace Topology

/-- A locally closed subset is open in the closure of itself, so its preimage under an
embedding whose image is that closure is open. -/
theorem IsEmbedding.isOpen_preimage_of_isLocallyClosed {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) {s : Set Y}
    (hs : IsLocallyClosed s) (hrange : Set.range f = closure s) : IsOpen (f ⁻¹' s) := by
  let e : X ≃ₜ ↥(closure s) := hf.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hpre : e ⁻¹' ((Subtype.val : closure s → Y) ⁻¹' s) = f ⁻¹' s := rfl
  rw [← hpre]
  exact e.isOpen_preimage.mpr hs.isOpen_preimage_val_closure

end Topology

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}}

/-- The identity morphism of a groupoid scheme. -/
def Hom.id (G : GroupoidScheme S) : Hom G G where
  mapObjects := 𝟙 G.objects
  mapArrows := 𝟙 G.arrows
  map_source := by rw [Category.id_comp, Category.comp_id]
  map_target := by rw [Category.id_comp, Category.comp_id]
  map_identity := by rw [Category.id_comp, Category.comp_id]
  map_comp T f g w w' := by
    have w₂ : f ≫ G.source = (g ≫ 𝟙 G.arrows) ≫ G.target := by
      simpa only [Category.comp_id] using w
    calc G.compose f g w ≫ 𝟙 G.arrows
        = G.compose f g w := Category.comp_id _
      _ = G.compose f (g ≫ 𝟙 G.arrows) w₂ :=
          compose_congr_right G (Category.comp_id g).symm w w₂
      _ = G.compose (f ≫ 𝟙 G.arrows) (g ≫ 𝟙 G.arrows) w' :=
          compose_congr_left G (Category.comp_id f).symm w₂ w'

/-- The identity morphism of a groupoid scheme is the identity on the scheme of objects. -/
@[simp]
theorem Hom.id_mapObjects (G : GroupoidScheme S) : (Hom.id G).mapObjects = 𝟙 G.objects := rfl

/-- The identity morphism of a groupoid scheme is the identity on the scheme of arrows. -/
@[simp]
theorem Hom.id_mapArrows (G : GroupoidScheme S) : (Hom.id G).mapArrows = 𝟙 G.arrows := rfl

/-- The identity morphism of a groupoid scheme is the identity on objects, written as the
identification morphism of the trivial identification. -/
theorem Hom.id_mapObjects_eqToHom (G : GroupoidScheme S) :
    (Hom.id G).mapObjects = eqToHom (rfl : G.objects = G.objects) := rfl

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry

/-! ### Identifications of schemes -/

/-- The underlying map of an identification of two schemes is surjective. -/
theorem surjective_base_eqToHom {X Y : Scheme.{u}} (e : X = Y) :
    Function.Surjective (eqToHom e).base := by
  cases e
  exact fun x => ⟨x, rfl⟩

/-! ### The reduced closure of the image of a morphism of groupoid schemes -/

variable {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}

/-- The reduced closure of the image on arrows of the identity morphism is the whole arrow
scheme. -/
theorem range_subschemeι_reducedClosureArrowImage_id (G : GroupoidScheme S) :
    Set.range (reducedClosureArrowImage (GroupoidScheme.Hom.id G)).subschemeι = Set.univ := by
  rw [range_subschemeι_reducedClosureArrowImage]
  have h : Set.range (GroupoidScheme.Hom.id G).mapArrows.left.base = Set.univ :=
    Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  rw [h, closure_univ]

/-- The image of the canonical morphism out of the reduced-closure groupoid is the closure of
the image on arrows. -/
theorem range_reducedClosureInclusion_mapArrows {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    Set.range (GroupoidScheme.reducedClosureInclusion F hobjects hfield
        hmapObjects).mapArrows.left.base = closure (Set.range F.mapArrows.left.base) := by
  have hsurj := surjective_base_eqToHom (congrArg Over.left
    (GroupoidScheme.reducedClosureGroupoid_arrows F hobjects hfield hmapObjects))
  rw [GroupoidScheme.reducedClosureInclusion_mapArrows_left,
    ← range_subschemeι_reducedClosureArrowImage F]
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨x, rfl⟩ := hy
    exact ⟨_, rfl⟩
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨z, rfl⟩ := hsurj x
    exact ⟨z, rfl⟩

/-- The canonical morphism out of the reduced-closure groupoid is a closed embedding on arrow
schemes. -/
theorem isClosedEmbedding_reducedClosureInclusion_mapArrows {k : Type u} [Field k]
    [PerfectField k] (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    Topology.IsClosedEmbedding (GroupoidScheme.reducedClosureInclusion F hobjects hfield
      hmapObjects).mapArrows.left.base := by
  rw [GroupoidScheme.reducedClosureInclusion_mapArrows_left]
  exact (IsClosedImmersion.isClosedEmbedding
      (reducedClosureArrowImage F).subschemeι).comp
    (isHomeomorph_base_eqToHom _).isClosedEmbedding

/-- A pair of morphisms over the base between the objects and the arrows of two groupoid
schemes, compatible with two morphisms to a third pair of groupoid schemes the second of which
is a monomorphism, is a morphism of groupoid schemes. -/
theorem GroupoidScheme.exists_hom_of_mono {H₁ H₂ : GroupoidScheme S}
    (J₁ : GroupoidScheme.Hom H₁ G₁) (J₂ : GroupoidScheme.Hom H₂ G₂)
    [Mono J₂.mapObjects] [Mono J₂.mapArrows] (F : GroupoidScheme.Hom G₁ G₂)
    (mapObjects : H₁.objects ⟶ H₂.objects) (mapArrows : H₁.arrows ⟶ H₂.arrows)
    (hobjects : mapObjects ≫ J₂.mapObjects = J₁.mapObjects ≫ F.mapObjects)
    (harrows : mapArrows ≫ J₂.mapArrows = J₁.mapArrows ≫ F.mapArrows) :
    ∃ F' : GroupoidScheme.Hom H₁ H₂,
      F'.mapObjects = mapObjects ∧ F'.mapArrows = mapArrows := by
  refine ⟨⟨mapObjects, mapArrows, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · refine (cancel_mono J₂.mapObjects).1 ?_
    rw [Category.assoc, ← J₂.map_source, ← Category.assoc, harrows, Category.assoc,
      F.map_source, ← Category.assoc, J₁.map_source, Category.assoc, ← hobjects,
      ← Category.assoc]
  · refine (cancel_mono J₂.mapObjects).1 ?_
    rw [Category.assoc, ← J₂.map_target, ← Category.assoc, harrows, Category.assoc,
      F.map_target, ← Category.assoc, J₁.map_target, Category.assoc, ← hobjects,
      ← Category.assoc]
  · refine (cancel_mono J₂.mapArrows).1 ?_
    rw [Category.assoc, ← J₂.map_identity, ← Category.assoc, hobjects, Category.assoc,
      F.map_identity, ← Category.assoc, J₁.map_identity, Category.assoc, ← harrows,
      ← Category.assoc]
  · intro T a b w w'
    have w₁ : (a ≫ J₁.mapArrows) ≫ G₁.source = (b ≫ J₁.mapArrows) ≫ G₁.target :=
      calc (a ≫ J₁.mapArrows) ≫ G₁.source
          = (a ≫ H₁.source) ≫ J₁.mapObjects := by
            simp only [Category.assoc, J₁.map_source]
        _ = (b ≫ H₁.target) ≫ J₁.mapObjects := congrArg (fun q => q ≫ J₁.mapObjects) w
        _ = (b ≫ J₁.mapArrows) ≫ G₁.target := by
            simp only [Category.assoc, J₁.map_target]
    have w₂ : ((a ≫ J₁.mapArrows) ≫ F.mapArrows) ≫ G₂.source =
        ((b ≫ J₁.mapArrows) ≫ F.mapArrows) ≫ G₂.target :=
      calc ((a ≫ J₁.mapArrows) ≫ F.mapArrows) ≫ G₂.source
          = ((a ≫ J₁.mapArrows) ≫ G₁.source) ≫ F.mapObjects := by
            simp only [Category.assoc, F.map_source]
        _ = ((b ≫ J₁.mapArrows) ≫ G₁.target) ≫ F.mapObjects :=
            congrArg (fun q => q ≫ F.mapObjects) w₁
        _ = ((b ≫ J₁.mapArrows) ≫ F.mapArrows) ≫ G₂.target := by
            simp only [Category.assoc, F.map_target]
    have ha : (a ≫ mapArrows) ≫ J₂.mapArrows = (a ≫ J₁.mapArrows) ≫ F.mapArrows := by
      simp only [Category.assoc, harrows]
    have hb : (b ≫ mapArrows) ≫ J₂.mapArrows = (b ≫ J₁.mapArrows) ≫ F.mapArrows := by
      simp only [Category.assoc, harrows]
    have wmid : ((a ≫ mapArrows) ≫ J₂.mapArrows) ≫ G₂.source =
        ((b ≫ J₁.mapArrows) ≫ F.mapArrows) ≫ G₂.target := by
      rwa [ha]
    have w₃ : ((a ≫ mapArrows) ≫ J₂.mapArrows) ≫ G₂.source =
        ((b ≫ mapArrows) ≫ J₂.mapArrows) ≫ G₂.target := by
      rwa [ha, hb]
    refine (cancel_mono J₂.mapArrows).1 ?_
    calc (H₁.compose a b w ≫ mapArrows) ≫ J₂.mapArrows
        = (H₁.compose a b w ≫ J₁.mapArrows) ≫ F.mapArrows := by
          simp only [Category.assoc, harrows]
      _ = G₁.compose (a ≫ J₁.mapArrows) (b ≫ J₁.mapArrows) w₁ ≫ F.mapArrows := by
          rw [J₁.map_comp]
      _ = G₂.compose ((a ≫ J₁.mapArrows) ≫ F.mapArrows)
            ((b ≫ J₁.mapArrows) ≫ F.mapArrows) w₂ := F.map_comp T _ _ w₁ w₂
      _ = G₂.compose ((a ≫ mapArrows) ≫ J₂.mapArrows)
            ((b ≫ J₁.mapArrows) ≫ F.mapArrows) wmid :=
          GroupoidScheme.compose_congr_left G₂ ha.symm w₂ wmid
      _ = G₂.compose ((a ≫ mapArrows) ≫ J₂.mapArrows)
            ((b ≫ mapArrows) ≫ J₂.mapArrows) w₃ :=
          GroupoidScheme.compose_congr_right G₂ hb.symm wmid w₃
      _ = H₂.compose (a ≫ mapArrows) (b ≫ mapArrows) w' ≫ J₂.mapArrows :=
          (J₂.map_comp T _ _ w' w₃).symm

/-- For a morphism of groupoid schemes over a perfect field which is the identity on the common
scheme of objects, the morphism between the reduced closure of the image of the identity and the
reduced closure of its own image, together with the identification of its map on objects and the
commuting square with the two closed immersions. -/
theorem exists_hom_reducedClosureGroupoid {k : Type u} [Field k] [PerfectField k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    ∃ F' : GroupoidScheme.Hom
        (GroupoidScheme.reducedClosureGroupoid (GroupoidScheme.Hom.id G₁) rfl hfield
          (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁))
        (GroupoidScheme.reducedClosureGroupoid F hobjects hfield hmapObjects),
      F'.mapObjects = eqToHom
          ((GroupoidScheme.reducedClosureGroupoid_objects (GroupoidScheme.Hom.id G₁) rfl hfield
              (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).trans
            (hobjects.trans (GroupoidScheme.reducedClosureGroupoid_objects F
              hobjects hfield hmapObjects).symm)) ∧
        F'.mapArrows ≫ (GroupoidScheme.reducedClosureInclusion F hobjects hfield
            hmapObjects).mapArrows =
          (GroupoidScheme.reducedClosureInclusion (GroupoidScheme.Hom.id G₁) rfl hfield
            (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).mapArrows ≫ F.mapArrows := by
  have hA₂ : (GroupoidScheme.reducedClosureGroupoid F hobjects hfield hmapObjects).arrows =
      reducedClosureArrows F :=
    GroupoidScheme.reducedClosureGroupoid_arrows F hobjects hfield hmapObjects
  have hJ₂ : (GroupoidScheme.reducedClosureInclusion F hobjects hfield hmapObjects).mapArrows =
      eqToHom hA₂ ≫ reducedClosureArrowsι F :=
    GroupoidScheme.reducedClosureInclusion_mapArrows F hobjects hfield hmapObjects
  have hJ₂o : (GroupoidScheme.reducedClosureInclusion F hobjects hfield
      hmapObjects).mapObjects = eqToHom
        (GroupoidScheme.reducedClosureGroupoid_objects F hobjects hfield hmapObjects) :=
    GroupoidScheme.reducedClosureInclusion_mapObjects F hobjects hfield hmapObjects
  have hred : IsReduced (GroupoidScheme.reducedClosureGroupoid (GroupoidScheme.Hom.id G₁) rfl
      hfield (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).arrows.left := by
    rw [show (GroupoidScheme.reducedClosureGroupoid (GroupoidScheme.Hom.id G₁) rfl hfield
        (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).arrows.left =
        (reducedClosureArrows (GroupoidScheme.Hom.id G₁)).left from
      congrArg Over.left (GroupoidScheme.reducedClosureGroupoid_arrows
        (GroupoidScheme.Hom.id G₁) rfl hfield
        (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁))]
    infer_instance
  obtain ⟨lift, hlift⟩ := GroupoidScheme.exists_lift_to_reducedClosureArrows F
    ((GroupoidScheme.reducedClosureInclusion (GroupoidScheme.Hom.id G₁) rfl hfield
      (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).mapArrows ≫ F.mapArrows) (by
      rintro z ⟨x, rfl⟩
      exact subset_closure ⟨_, rfl⟩)
  have harrows : (lift ≫ eqToHom hA₂.symm) ≫
      (GroupoidScheme.reducedClosureInclusion F hobjects hfield hmapObjects).mapArrows =
      (GroupoidScheme.reducedClosureInclusion (GroupoidScheme.Hom.id G₁) rfl hfield
        (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).mapArrows ≫ F.mapArrows := by
    rw [hJ₂]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact hlift
  have hobjmap : eqToHom ((GroupoidScheme.reducedClosureGroupoid_objects
          (GroupoidScheme.Hom.id G₁) rfl hfield
          (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).trans
        (hobjects.trans (GroupoidScheme.reducedClosureGroupoid_objects F
          hobjects hfield hmapObjects).symm)) ≫
      (GroupoidScheme.reducedClosureInclusion F hobjects hfield hmapObjects).mapObjects =
      (GroupoidScheme.reducedClosureInclusion (GroupoidScheme.Hom.id G₁) rfl hfield
        (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).mapObjects ≫ F.mapObjects := by
    rw [hJ₂o, GroupoidScheme.reducedClosureInclusion_mapObjects, hmapObjects, eqToHom_trans,
      eqToHom_trans]
  have hmonoArrows : Mono (GroupoidScheme.reducedClosureInclusion F hobjects hfield
      hmapObjects).mapArrows := by
    rw [hJ₂]; infer_instance
  have hmonoObjects : Mono (GroupoidScheme.reducedClosureInclusion F hobjects hfield
      hmapObjects).mapObjects := by
    rw [hJ₂o]; infer_instance
  obtain ⟨F', hF'o, hF'a⟩ := GroupoidScheme.exists_hom_of_mono
    (GroupoidScheme.reducedClosureInclusion (GroupoidScheme.Hom.id G₁) rfl hfield
      (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁))
    (GroupoidScheme.reducedClosureInclusion F hobjects hfield hmapObjects) F _ _
    hobjmap harrows
  exact ⟨F', hF'o, hF'a ▸ harrows⟩

/-! ### Locally closed images -/

/-- If the range of `f'` is the preimage of the range of `f` under a closed embedding `j` whose
range contains the range of `f`, and the range of `f'` is closed, then the range of `f` is
closed. -/
private theorem isClosed_range_of_range_eq_preimage {X X' Y' Y : Type*} [TopologicalSpace Y']
    [TopologicalSpace Y] {f' : X' → Y'} {f : X → Y} {j : Y' → Y}
    (hj : Topology.IsClosedEmbedding j) (hrange : Set.range f' = j ⁻¹' Set.range f)
    (hsub : Set.range f ⊆ Set.range j) (hclosed : IsClosed (Set.range f')) :
    IsClosed (Set.range f) := by
  have himage : j '' Set.range f' = Set.range f := by
    rw [hrange, Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_left.2 hsub
  rw [← himage]
  exact hj.isClosedMap _ hclosed

/-- **Stacks Project, Tag 04Q9** over a perfect field. The image on arrows of a morphism of
groupoid schemes over a perfect field which is the identity on the common scheme of objects is
closed as soon as it is locally closed. -/
theorem isClosed_range_mapArrows_of_isLocallyClosed_of_perfectField {k : Type u} [Field k]
    [PerfectField k] (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects)
    (h : IsLocallyClosed (Set.range F.mapArrows.left.base)) :
    IsClosed (Set.range F.mapArrows.left.base) := by
  obtain ⟨Fbar, hbarObj, hbarArr⟩ :=
    exists_hom_reducedClosureGroupoid F hobjects hfield hmapObjects
  have hJ₁range : Set.range (GroupoidScheme.reducedClosureInclusion
      (GroupoidScheme.Hom.id G₁) rfl hfield
      (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).mapArrows.left.base = Set.univ := by
    rw [range_reducedClosureInclusion_mapArrows, Set.range_eq_univ.mpr
      (fun x => ⟨x, rfl⟩ : Function.Surjective (GroupoidScheme.Hom.id G₁).mapArrows.left.base),
      closure_univ]
  have hJ₂range : Set.range (GroupoidScheme.reducedClosureInclusion F hobjects hfield
      hmapObjects).mapArrows.left.base = closure (Set.range F.mapArrows.left.base) :=
    range_reducedClosureInclusion_mapArrows F hobjects hfield hmapObjects
  have hJ₂emb : Topology.IsClosedEmbedding (GroupoidScheme.reducedClosureInclusion F hobjects
      hfield hmapObjects).mapArrows.left.base :=
    isClosedEmbedding_reducedClosureInclusion_mapArrows F hobjects hfield hmapObjects
  have hpoint : ∀ x, (GroupoidScheme.reducedClosureInclusion F hobjects hfield
      hmapObjects).mapArrows.left.base (Fbar.mapArrows.left.base x) =
      F.mapArrows.left.base ((GroupoidScheme.reducedClosureInclusion
        (GroupoidScheme.Hom.id G₁) rfl hfield
        (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)).mapArrows.left.base x) := fun x =>
    congrArg (fun f : Scheme.Hom _ _ => f.base x) (congrArg Over.Hom.left hbarArr)
  have hbarRange : Set.range Fbar.mapArrows.left.base =
      (GroupoidScheme.reducedClosureInclusion F hobjects hfield
        hmapObjects).mapArrows.left.base ⁻¹' Set.range F.mapArrows.left.base :=
    Set.range_eq_preimage_range_of_comm hpoint (Set.range_eq_univ.mp hJ₁range)
      hJ₂emb.injective
  have hopen : IsOpen (Set.range Fbar.mapArrows.left.base) := by
    rw [hbarRange]
    exact hJ₂emb.isEmbedding.isOpen_preimage_of_isLocallyClosed h hJ₂range
  have hclosedbar : IsClosed (Set.range Fbar.mapArrows.left.base) :=
    isClosed_range_mapArrows_of_isOpen Fbar _
      ((GroupoidScheme.reducedClosureGroupoid_objects (GroupoidScheme.Hom.id G₁) rfl hfield
        (GroupoidScheme.Hom.id_mapObjects_eqToHom G₁)) ▸ hfield) hbarObj hopen
  exact isClosed_range_of_range_eq_preimage hJ₂emb hbarRange
    (hJ₂range ▸ subset_closure) hclosedbar

/-- **Stacks Project, Tag 04Q9.** The image on arrows of a morphism of groupoid schemes over a
field which is the identity on their common scheme of objects is closed as soon as it is
locally closed. -/
@[stacks 04Q9]
theorem isClosed_range_mapArrows_of_isLocallyClosed {k : Type u} [Field k]
    (F : GroupoidScheme.Hom G₁ G₂) (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects)
    (h : IsLocallyClosed (Set.range F.mapArrows.left.base)) :
    IsClosed (Set.range F.mapArrows.left.base) := by
  let K : Type u := perfectClosure k (AlgebraicClosure k)
  have hfield₂ : G₂.objects.left = Spec (.of k) :=
    (congrArg Over.left hobjects).symm.trans hfield
  let φ : Spec (.of K) ⟶ G₁.objects.left :=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ eqToHom hfield.symm
  have hφ : UniversallyInjective φ :=
    MorphismProperty.comp_mem _ _ _ (universallyInjective_specMap_algebraMap k K)
      inferInstance
  let U' : Over S := Over.mk (φ ≫ G₁.objects.hom)
  let g₁ : U' ⟶ G₁.objects := Over.homMk φ rfl
  let g₂ : U' ⟶ G₂.objects := g₁ ≫ F.mapObjects
  have hg₁ : UniversallyInjective g₁.left := hφ
  have hg₂ : UniversallyInjective g₂.left :=
    overFibreProduct_comp g₁ F.mapObjects hφ (by rw [hmapObjects]; infer_instance)
  have hR₁homeo : IsHomeomorph (GroupoidScheme.restrict G₁ g₁).hom.mapArrows.left.base :=
    GroupoidScheme.isHomeomorph_mapArrows_restrict G₁ g₁ k K (eqToIso hfield) (Iso.refl _)
  have hR₂homeo : IsHomeomorph (GroupoidScheme.restrict G₂ g₂).hom.mapArrows.left.base :=
    GroupoidScheme.isHomeomorph_mapArrows_restrict G₂ g₂ k K (eqToIso hfield₂) (Iso.refl _)
  obtain ⟨F', hF'obj, hF'arr⟩ := GroupoidScheme.restrictHom F g₁ g₂ rfl
  have hfield' : (GroupoidScheme.restrict G₁ g₁).groupoid.objects.left = Spec (.of K) :=
    congrArg Over.left (GroupoidScheme.restrict G₁ g₁).objects_eq
  have hpoint : ∀ z, (GroupoidScheme.restrict G₂ g₂).hom.mapArrows.left.base
      (F'.mapArrows.left.base z) =
      F.mapArrows.left.base ((GroupoidScheme.restrict G₁ g₁).hom.mapArrows.left.base z) :=
    fun z => congrArg (fun q : Scheme.Hom _ _ => q.base z) hF'arr
  have hrange : Set.range F'.mapArrows.left.base =
      (GroupoidScheme.restrict G₂ g₂).hom.mapArrows.left.base ⁻¹'
        Set.range F.mapArrows.left.base :=
    Set.range_eq_preimage_range_of_comm hpoint hR₁homeo.surjective hR₂homeo.injective
  have hclosed' : IsClosed (Set.range F'.mapArrows.left.base) :=
    isClosed_range_mapArrows_of_isLocallyClosed_of_perfectField (k := K) F'
      ((GroupoidScheme.restrict G₁ g₁).objects_eq.trans
        (GroupoidScheme.restrict G₂ g₂).objects_eq.symm) hfield' hF'obj
      (by rw [hrange]; exact h.preimage hR₂homeo.continuous)
  exact isClosed_range_of_range_eq_preimage hR₂homeo.isClosedEmbedding hrange
    (fun y _ => hR₂homeo.surjective y) hclosed'

end AlgebraicGeometry

end
