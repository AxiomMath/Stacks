module

public import StacksFrontier.AlgebraicGeometry.Limits.ImageSystemLimit
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# A closed subscheme of a cofiltered limit is the limit of its images at the stages

Let `c` be a limit cone on a cofiltered diagram `N` of schemes with affine transition morphisms,
so that `c.pt = lim N`, and let `i : Z ⟶ c.pt` be a closed immersion. The scheme-theoretic
images of `Z` in the stages form an inverse system of closed subschemes `Z_k ⊆ N.obj k`, and the
canonical cone with vertex `Z` on that system is a limit cone: `lim Z_k = Z`.

## Main definitions

* `AlgebraicGeometry.closedSubschemeImageSystem`: the inverse system `k ↦ Z_k` of the
  scheme-theoretic images of `Z` in the stages.
* `AlgebraicGeometry.closedSubschemeImageSystemι`: the closed immersions `Z_k ⟶ N.obj k`, as a
  morphism of systems.
* `AlgebraicGeometry.closedSubschemeImageCone`: the cone with vertex `Z` whose leg at `k` is the
  canonical morphism `Z ⟶ Z_k`.

## Main results

* `AlgebraicGeometry.isLimit_closedSubschemeImageCone`: that cone is a limit cone.

## References

* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 056A](https://stacks.math.columbia.edu/tag/056A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-! ### The inverse system of scheme-theoretic images -/

section System

variable {K : Type v} [Category.{w} K] (N : K ⥤ Scheme.{u}) (c : Cone N) {Z : Scheme.{u}}
  (i : Z ⟶ c.pt)

/-- The transition morphism of the system of scheme-theoretic images of `Z` in the stages: the
image of `Z` in `N.obj j` is carried into the image of `Z` in `N.obj k` by the transition
morphism of the diagram. -/
noncomputable def closedSubschemeImageTransition {j k : K} (a : j ⟶ k) :
    (i ≫ c.π.app j).image ⟶ (i ≫ c.π.app k).image :=
  Scheme.Hom.imageMap (i ≫ c.π.app j) (i ≫ c.π.app k) (𝟙 Z) (N.map a)
    (by rw [Category.id_comp, Category.assoc, c.w a])

/-- The transition morphism of the system of images, followed by the closed immersion of the
image into `N.obj k`, is the closed immersion of the image into `N.obj j` followed by the
transition morphism of the diagram. -/
@[reassoc (attr := simp)]
lemma closedSubschemeImageTransition_imageι {j k : K} (a : j ⟶ k) :
    closedSubschemeImageTransition N c i a ≫ (i ≫ c.π.app k).imageι =
      (i ≫ c.π.app j).imageι ≫ N.map a :=
  Scheme.Hom.imageMap_imageι _ _ _ _ _

/-- The canonical morphism from `Z` to its image in `N.obj j`, followed by the transition
morphism of the system of images, is the canonical morphism from `Z` to its image in `N.obj k`. -/
@[reassoc (attr := simp)]
lemma toImage_closedSubschemeImageTransition {j k : K} (a : j ⟶ k) :
    (i ≫ c.π.app j).toImage ≫ closedSubschemeImageTransition N c i a =
      (i ≫ c.π.app k).toImage := by
  rw [closedSubschemeImageTransition, Scheme.Hom.toImage_imageMap, Category.id_comp]

/-- The transition morphisms of the system of images are affine when those of the diagram
are. -/
lemma isAffineHom_closedSubschemeImageTransition {j k : K} (a : j ⟶ k) [IsAffineHom (N.map a)] :
    IsAffineHom (closedSubschemeImageTransition N c i a) :=
  Scheme.Hom.isAffineHom_imageMap _ _ _ _ _

/-- The inverse system of the scheme-theoretic images of the closed subscheme `Z` of the limit in
the stages of the diagram. -/
@[reducible] noncomputable def closedSubschemeImageSystem : K ⥤ Scheme.{u} where
  obj k := (i ≫ c.π.app k).image
  map a := closedSubschemeImageTransition N c i a
  map_id k := by
    refine (cancel_mono (i ≫ c.π.app k).imageι).mp ?_
    rw [closedSubschemeImageTransition_imageι, N.map_id, Category.comp_id, Category.id_comp]
  map_comp {j k l} a b := by
    refine (cancel_mono (i ≫ c.π.app l).imageι).mp ?_
    rw [closedSubschemeImageTransition_imageι, Category.assoc,
      closedSubschemeImageTransition_imageι, closedSubschemeImageTransition_imageι_assoc,
      N.map_comp]

/-- The transition morphisms of the system of images are affine when those of the diagram are. -/
instance isAffineHom_closedSubschemeImageSystem_map {j k : K} (a : j ⟶ k)
    [IsAffineHom (N.map a)] : IsAffineHom ((closedSubschemeImageSystem N c i).map a) :=
  isAffineHom_closedSubschemeImageTransition N c i a

/-- The closed immersions of the images into the stages, as a morphism of systems. -/
noncomputable def closedSubschemeImageSystemι : closedSubschemeImageSystem N c i ⟶ N where
  app k := (i ≫ c.π.app k).imageι
  naturality _ _ a := closedSubschemeImageTransition_imageι N c i a

/-- The component at `k` of `closedSubschemeImageSystemι` is the closed immersion of the image of
`Z` into `N.obj k`. -/
lemma closedSubschemeImageSystemι_app (k : K) :
    (closedSubschemeImageSystemι N c i).app k = (i ≫ c.π.app k).imageι :=
  rfl

/-- Each component of `closedSubschemeImageSystemι` is a closed immersion. -/
instance isClosedImmersion_closedSubschemeImageSystemι_app (k : K) :
    IsClosedImmersion ((closedSubschemeImageSystemι N c i).app k) :=
  inferInstanceAs (IsClosedImmersion (i ≫ c.π.app k).imageι)

/-- The cone with vertex the closed subscheme `Z` on the system of its images in the stages, whose
leg at `k` is the canonical morphism from `Z` to its image in `N.obj k`. -/
@[reducible] noncomputable def closedSubschemeImageCone :
    Cone (closedSubschemeImageSystem N c i) where
  pt := Z
  π :=
    { app := fun k => (i ≫ c.π.app k).toImage
      naturality := fun j k a => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.id_comp]
        exact (toImage_closedSubschemeImageTransition N c i a).symm }

/-- The leg at `k` of `closedSubschemeImageCone`, followed by the closed immersion of the image
into `N.obj k`, is `i ≫ c.π.app k`. -/
@[reassoc (attr := simp)]
lemma closedSubschemeImageCone_π_app_comp_imageι (k : K) :
    (closedSubschemeImageCone N c i).π.app k ≫ (closedSubschemeImageSystemι N c i).app k =
      i ≫ c.π.app k :=
  Scheme.Hom.toImage_imageι _

end System

/-! ### The cone is limiting -/

section IsLimit

variable {K : Type v} [Category.{w} K] [IsCofiltered K] (N : K ⥤ Scheme.{u})
  [∀ {a b : K} (h : a ⟶ b), IsAffineHom (N.map h)] (c : Cone N) {Z : Scheme.{u}}
  (i : Z ⟶ c.pt) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- The ideal sheaf of `Z` in the limit is contained in the supremum of the inverse images of the
ideal sheaves of the images of `Z` at the stages. -/
private lemma ker_le_iSup_ker_comap (hc : IsLimit c) :
    i.ker ≤ ⨆ k : K, (i ≫ c.π.app k).ker.comap (c.π.app k) := by
  refine (le_iSup_comap_map_of_isLimit N c hc i.ker).trans (iSup_le fun k => ?_)
  rw [← Scheme.Hom.ker_comp]
  exact le_iSup (fun k : K => (i ≫ c.π.app k).ker.comap (c.π.app k)) k

/-- The morphism to the limit induced by a cone on the system of images. -/
private noncomputable def coneLiftAux (hc : IsLimit c)
    (s : Cone (closedSubschemeImageSystem N c i)) : s.pt ⟶ c.pt :=
  hc.lift ((Cone.postcompose (closedSubschemeImageSystemι N c i)).obj s)

omit [IsCofiltered K] [∀ {a b : K} (h : a ⟶ b), IsAffineHom (N.map h)] [IsClosedImmersion i] in
private lemma coneLiftAux_comp_π_app (hc : IsLimit c)
    (s : Cone (closedSubschemeImageSystem N c i)) (k : K) :
    coneLiftAux N c i hc s ≫ c.π.app k = s.π.app k ≫ (i ≫ c.π.app k).imageι :=
  hc.fac _ k

omit [IsCofiltered K] [∀ {a b : K} (h : a ⟶ b), IsAffineHom (N.map h)] [IsClosedImmersion i] in
/-- The supremum of the inverse images of the ideal sheaves of the images of `Z` is contained in
the kernel of the morphism to the limit induced by a cone on the system of images. -/
private lemma iSup_ker_comap_le_ker_coneLiftAux (hc : IsLimit c)
    (s : Cone (closedSubschemeImageSystem N c i)) :
    (⨆ k : K, (i ≫ c.π.app k).ker.comap (c.π.app k)) ≤ (coneLiftAux N c i hc s).ker := by
  refine iSup_le fun k => ?_
  calc (i ≫ c.π.app k).ker.comap (c.π.app k)
      = (pullback.fst (c.π.app k) (i ≫ c.π.app k).imageι).ker := rfl
    _ ≤ (pullback.lift (coneLiftAux N c i hc s) (s.π.app k)
            (coneLiftAux_comp_π_app N c i hc s k) ≫
          pullback.fst (c.π.app k) (i ≫ c.π.app k).imageι).ker :=
        Scheme.Hom.le_ker_comp _ _
    _ = (coneLiftAux N c i hc s).ker := congrArg Scheme.Hom.ker (pullback.lift_fst _ _ _)

/-- The morphism from the vertex of a cone on the system of images to `Z`. -/
private noncomputable def coneLift (hc : IsLimit c)
    (s : Cone (closedSubschemeImageSystem N c i)) : s.pt ⟶ Z :=
  IsClosedImmersion.lift i (coneLiftAux N c i hc s)
    ((ker_le_iSup_ker_comap N c i hc).trans (iSup_ker_comap_le_ker_coneLiftAux N c i hc s))

private lemma coneLift_comp (hc : IsLimit c) (s : Cone (closedSubschemeImageSystem N c i)) :
    coneLift N c i hc s ≫ i = coneLiftAux N c i hc s :=
  IsClosedImmersion.lift_fac _ _ _

private lemma coneLift_fac (hc : IsLimit c) (s : Cone (closedSubschemeImageSystem N c i))
    (k : K) : coneLift N c i hc s ≫ (i ≫ c.π.app k).toImage = s.π.app k := by
  refine (cancel_mono (i ≫ c.π.app k).imageι).mp ?_
  rw [Category.assoc, Scheme.Hom.toImage_imageι, ← Category.assoc, coneLift_comp,
    coneLiftAux_comp_π_app]

private lemma coneLift_uniq (hc : IsLimit c) (s : Cone (closedSubschemeImageSystem N c i))
    (m : s.pt ⟶ Z) (hm : ∀ k, m ≫ (i ≫ c.π.app k).toImage = s.π.app k) :
    m = coneLift N c i hc s := by
  have key (k : K) : m ≫ i ≫ c.π.app k = coneLiftAux N c i hc s ≫ c.π.app k := by
    rw [coneLiftAux_comp_π_app, ← hm k, Category.assoc, Scheme.Hom.toImage_imageι]
  refine (cancel_mono i).mp (hc.hom_ext fun k => ?_)
  rw [Category.assoc, key k, coneLift_comp]

/-- Let `c` be a limit cone on a cofiltered diagram `N` of schemes with affine transition
morphisms and let `i : Z ⟶ c.pt` be a closed immersion. Then the cone with vertex `Z` on the
system of scheme-theoretic images of `Z` in the stages is a limit cone: `lim Z_k = Z`. -/
@[no_expose]
noncomputable def isLimit_closedSubschemeImageCone (hc : IsLimit c) :
    IsLimit (closedSubschemeImageCone N c i) where
  lift := coneLift N c i hc
  fac := coneLift_fac N c i hc
  uniq s m hm := coneLift_uniq N c i hc s m hm

end IsLimit

end AlgebraicGeometry

end
