module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Images in a functor category are computed pointwise

If a category `C` has images and those images are functorial, then any functor category `J ⥤ C`
has images, computed pointwise: the image of a natural transformation is the functor sending `j`
to the image of its component at `j`, with the pointwise inclusions and corestrictions.

Mathlib proves this for `C = Type*` only
(`CategoryTheory.FunctorToTypes.instHasImagesFunctorType`), by a construction specific to
`CategoryTheory.Subfunctor`.  The statement below is the same fact for a general target.

## Main definitions

* `Stacks.FunctorImages.imageSq`: a naturality square of a natural transformation, read as a
  morphism in the arrow category of `C`.
* `Stacks.FunctorImages.imageFunctor`: the pointwise image of a natural transformation.
* `Stacks.FunctorImages.imageInclusion` and `Stacks.FunctorImages.imageProjection`: the two legs
  of the pointwise factorisation.
* `Stacks.FunctorImages.appMonoFactorisation`: a mono factorisation in `J ⥤ C`, evaluated at an
  object of `J`.
* `Stacks.FunctorImages.liftNatTrans` and `Stacks.FunctorImages.isImage`: the pointwise image is
  the image.

## Main results

* `Stacks.FunctorImages.hasImages`: `J ⥤ C` has images whenever `C` has images, functorial
  images and pullbacks.

## Implementation notes

Two hypotheses beyond `CategoryTheory.Limits.HasImages C` are needed, for two different reasons.
`CategoryTheory.Limits.HasImageMaps C` makes the pointwise image a *functor*: without it there
is no morphism between the images of two components, so `imageFunctor` has no action on
morphisms.  `CategoryTheory.Limits.HasPullbacks C` is what makes a monomorphism in `J ⥤ C`
pointwise monomorphic, via `CategoryTheory.NatTrans.mono_iff_mono_app`; being a monomorphism is a
pullback condition, so this direction is not formal.  The converse direction is formal and is
`CategoryTheory.NatTrans.mono_of_mono_app`, used for `imageInclusion`.  So `HasPullbacks` is
confined to the section that constructs the universal property, and the factorisation itself does
not need it.

`imageFunctor` and `appMonoFactorisation` are `@[reducible]`, and this is load-bearing rather
than cosmetic.  Both appear in the *types* of the morphisms being composed in the naturality
proof of `liftNatTrans`: `image.lift (appMonoFactorisation F' j)` lands in
`(appMonoFactorisation F' j).I`, which is `F'.I.obj j` only after the definition is unfolded.
`rw` and `simp` elaborate their congruence motives at `implicit` transparency, which does not
unfold a semireducible definition, so with plain `def` every rewrite in that proof fails with an
application type mismatch -- including `CategoryTheory.Category.assoc`, which is why the failure
looks unrelated to the definitions.  Marking the two definitions reducible is what lets the proof
be a rewrite chain instead of an explicit term.

`imageFunctor` is given its fields directly rather than defined as
`arrowDiagram f ⋙ CategoryTheory.Limits.im`, which would supply functoriality for free: the
composite's object part is not syntactically `image (f.app j)`, and the same transparency problem
then appears one level further in.  The price is `imageSq_id` and `imageSq_comp`, both one-liners
from `CategoryTheory.Arrow.hom_ext`.

## References

* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.FunctorImages

noncomputable section

variable {J : Type*} [Category J] {C : Type*} [Category C]
  [HasImages C] [HasImageMaps C] {F G : J ⥤ C}

/-- A naturality square of `f`, read as a morphism in the arrow category of `C` from the
component of `f` at `a` to its component at `b`. -/
def imageSq (f : F ⟶ G) {a b : J} (φ : a ⟶ b) :
    Arrow.mk (f.app a) ⟶ Arrow.mk (f.app b) :=
  Arrow.homMk' (F.map φ) (G.map φ) (f.naturality φ)

omit [HasImages C] [HasImageMaps C] in
/-- The right leg of `imageSq f φ` is `G.map φ`. -/
@[simp]
theorem imageSq_right (f : F ⟶ G) {a b : J} (φ : a ⟶ b) :
    Arrow.Hom.right (imageSq f φ) = G.map φ :=
  rfl

omit [HasImages C] [HasImageMaps C] in
/-- The left leg of `imageSq f φ` is `F.map φ`. -/
@[simp]
theorem imageSq_left (f : F ⟶ G) {a b : J} (φ : a ⟶ b) :
    Arrow.Hom.left (imageSq f φ) = F.map φ :=
  rfl

omit [HasImages C] [HasImageMaps C] in
/-- The naturality square of `f` at an identity morphism is the identity of the arrow `f.app j`. -/
theorem imageSq_id (f : F ⟶ G) (j : J) : imageSq f (𝟙 j) = 𝟙 (Arrow.mk (f.app j)) :=
  Arrow.hom_ext _ _ (F.map_id j) (G.map_id j)

omit [HasImages C] [HasImageMaps C] in
/-- The naturality square of `f` at a composite is the composite of the naturality squares. -/
theorem imageSq_comp (f : F ⟶ G) {a b c : J} (φ : a ⟶ b) (ψ : b ⟶ c) :
    imageSq f (φ ≫ ψ) = imageSq f φ ≫ imageSq f ψ :=
  Arrow.hom_ext _ _ (F.map_comp φ ψ) (G.map_comp φ ψ)

/-- **The pointwise image of a natural transformation.**  Its value at `j` is the image of the
component of `f` at `j`, and its action on a morphism is the induced morphism of images. -/
@[reducible]
def imageFunctor (f : F ⟶ G) : J ⥤ C where
  obj j := image (f.app j)
  map φ := image.map (imageSq f φ)
  map_id j := by rw [imageSq_id]; exact image.map_id _
  map_comp φ ψ := by rw [imageSq_comp]; exact image.map_comp _ _

/-- The inclusion of the pointwise image into the target, a monomorphism of functors. -/
def imageInclusion (f : F ⟶ G) : imageFunctor f ⟶ G where
  app j := image.ι (f.app j)
  naturality _ _ φ := image.map_ι (imageSq f φ)

/-- The corestriction of a natural transformation to its pointwise image. -/
def imageProjection (f : F ⟶ G) : F ⟶ imageFunctor f where
  app j := factorThruImage (f.app j)
  naturality _ _ φ := (image.factor_map (imageSq f φ)).symm

/-- The inclusion of the pointwise image into the target is a monomorphism. -/
instance monoImageInclusion (f : F ⟶ G) : Mono (imageInclusion f) :=
  have : ∀ j, Mono ((imageInclusion f).app j) := fun j =>
    show Mono (image.ι (f.app j)) from inferInstance
  NatTrans.mono_of_mono_app _

/-- The pointwise factorisation of a natural transformation through a monomorphism. -/
def monoFactorisation (f : F ⟶ G) : MonoFactorisation f where
  I := imageFunctor f
  m := imageInclusion f
  e := imageProjection f
  fac := by ext j; exact image.fac (f.app j)

section

variable [HasPullbacks C]

/-- A mono factorisation in `J ⥤ C`, evaluated at an object of `J`.  Its middle morphism is a
monomorphism because a monomorphism of functors into a category with pullbacks is pointwise
monomorphic. -/
@[reducible]
def appMonoFactorisation {f : F ⟶ G} (F' : MonoFactorisation f) (j : J) :
    MonoFactorisation (f.app j) where
  I := F'.I.obj j
  m := F'.m.app j
  m_mono := ((NatTrans.mono_iff_mono_app F'.m).mp F'.m_mono) j
  e := F'.e.app j
  fac := by rw [← NatTrans.comp_app, F'.fac]

omit [HasImageMaps C] in
/-- The lift of the image of `f.app j` into the factorisation `F'` at `j`, composed with the
middle morphism of `F'` at `j`, is the inclusion of the image of `f.app j`. -/
@[reassoc (attr := simp)]
theorem liftApp_fac {f : F ⟶ G} (F' : MonoFactorisation f) (j : J) :
    image.lift (appMonoFactorisation F' j) ≫ F'.m.app j = image.ι (f.app j) :=
  image.lift_fac _

/-- **The comparison morphism from the pointwise image into any other mono factorisation.**  Its
component at `j` is the lift of the image of `f.app j` into the factorisation at `j`. -/
def liftNatTrans {f : F ⟶ G} (F' : MonoFactorisation f) : imageFunctor f ⟶ F'.I where
  app j := image.lift (appMonoFactorisation F' j)
  naturality a b φ := by
    have hm : Mono (F'.m.app b) := (appMonoFactorisation F' b).m_mono
    rw [← cancel_mono (F'.m.app b)]
    simp only [Category.assoc, liftApp_fac, F'.m.naturality, liftApp_fac_assoc]
    exact image.map_ι (imageSq f φ)

/-- **The pointwise image of a natural transformation is its image.** -/
def isImage (f : F ⟶ G) : IsImage (monoFactorisation f) where
  lift F' := liftNatTrans F'
  lift_fac F' := by ext j; exact image.lift_fac (appMonoFactorisation F' j)

/-- A natural transformation between functors into `C` has an image. -/
instance hasImage (f : F ⟶ G) : HasImage f :=
  HasImage.mk ⟨_, isImage f⟩

/-- **A functor category has images whenever its target has functorial images and pullbacks.** -/
instance hasImages : HasImages (J ⥤ C) where
  has_image f := hasImage f

end

end

end Stacks.FunctorImages
