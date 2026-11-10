module

public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Simplicial.Site

/-!
# The fibre of a simplicial space over an open of the augmentation target

Let `X` be a simplicial topological space, let `a : X ⟶ Y` be an augmentation towards a
topological space `Y`, and let `V` be an open of `Y`.  The fibre product `X ×_Y V` is the
simplicial space whose degree-`n` space is the open subspace `a_n⁻¹(V)` of `X_n`; the
augmentation equation `X(φ) ≫ a_m = a_n` is what makes the simplicial structure maps of `X`
restrict to it.

This file constructs that simplicial space, the levelwise open immersion `j : X ×_Y V ⟶ X`,
and the comparison of their total sites of Stacks 09VL: an object of the site of `X ×_Y V` is
an open of a space `a_n⁻¹(V)`, and the comparison sends it to the open of `X_n` it cuts out.
The comparison is fully faithful, is *downwards closed* — any object of the site of `X` that
admits an arrow into its image is already in its image — and is a continuous functor of sites.

## Main definitions

* `Stacks.Topology.Simplicial.fibreOpens`: the open `a_n⁻¹(V)` of `X_n`.
* `Stacks.Topology.Simplicial.fibreSpace`: the simplicial space `X ×_Y V`.
* `Stacks.Topology.Simplicial.fibreInclusion`: the levelwise open immersion `X ×_Y V ⟶ X`.
* `Stacks.Topology.Simplicial.fibreImage`: the comparison `(X ×_Y V)_Zar ⥤ X_Zar` of total
  sites.

## Main results

* `Stacks.Topology.Simplicial.fibreImage_fullyFaithful`: the comparison is fully faithful.
* `Stacks.Topology.Simplicial.fibreImage_downwardsClosed`: an object of `X_Zar` admitting an
  arrow into the image of the comparison is itself in the image, with an explicit preimage.
* `Stacks.Topology.Simplicial.fibreImage_coverPreserving` and
  `Stacks.Topology.Simplicial.fibreImage_isContinuous`: the comparison is a continuous functor
  of sites.

## Implementation notes

Downwards closure is the geometric content of the fibre being a fibre *product*: an arrow
`(n, U) ⟶ (m, W)` of the site of `X` with `W ⊆ a_m⁻¹(V)` has `a_n(U) = a_m(X(φ)(U)) ⊆ V`, so
`U ⊆ a_n⁻¹(V)`.  It is what replaces representable flatness in the proof that the comparison is
continuous: the functor is *not* representably flat, the structured-arrow category over an
object outside the fibre being empty, so `CategoryTheory.Functor.isContinuous_iff_coverPreserving`
does not apply; `CategoryTheory.compatiblePreservingOfDownwardsClosed` does.

Points of the open subspace `a_n⁻¹(V)` are handled through `fibrePt` and `fibreMk` rather than
through `Subtype.val` and the anonymous constructor, as in
`Stacks.Topology.Simplicial.DiagramOpen`: the object `(fibreSpace X Y a V).obj n` of `TopCat` is
produced by a definition, so the elaborator does not see a subtype there.

## References

* [Stacks Project, Tag 0D84](https://stacks.math.columbia.edu/tag/0D84)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

variable (X : SimplicialObject TopCat.{u}) (Y : TopCat.{u})
  (a : X ⟶ (SimplicialObject.const TopCat).obj Y) (V : Opens Y)

/-- The open `a_n⁻¹(V)` of the degree-`n` space of a simplicial space augmented towards `Y`.
As a subspace, it is the degree-`n` space of the fibre product `X ×_Y V`. -/
abbrev fibreOpens (n : SimplexCategoryᵒᵖ) : Opens (X.obj n) :=
  (Opens.map (a.app n)).obj V

/-- An augmentation of a simplicial space is a cocone, so the simplicial structure maps are
compatible with it. -/
theorem augmentation_comp_app {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    X.map φ ≫ a.app m = a.app n :=
  (show Cocone X from { pt := Y, ι := a }).w φ

/-- The augmentation is invariant under the simplicial structure maps, pointwise. -/
private theorem augmentation_app_map_apply {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (x : X.obj n) :
    a.app m (X.map φ x) = a.app n x :=
  ConcreteCategory.congr_hom (augmentation_comp_app X Y a φ) x

/-- The simplicial structure maps of `X` carry `a_n⁻¹(V)` into `a_m⁻¹(V)`. -/
theorem fibreSpace_mapsTo {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (x : ↥(fibreOpens X Y a V n)) : X.map φ x.1 ∈ fibreOpens X Y a V m := by
  change a.app m (X.map φ x.1) ∈ V
  rw [augmentation_app_map_apply X Y a φ]
  exact x.2

/-- **The fibre product `X ×_Y V` of a simplicial space with an open of its augmentation
target.** Its degree-`n` space is the open subspace `a_n⁻¹(V)` of `X_n`, and a simplex map acts
by restricting the corresponding structure map of `X`. -/
def fibreSpace : SimplicialObject TopCat.{u} where
  obj n := TopCat.of ↥(fibreOpens X Y a V n)
  map φ := TopCat.ofHom
    ⟨fun x => ⟨X.map φ x.1, fibreSpace_mapsTo X Y a V φ x⟩,
      Continuous.subtype_mk ((X.map φ).hom.continuous.comp continuous_subtype_val)
        (fibreSpace_mapsTo X Y a V φ)⟩
  map_id n := TopCat.hom_ext (ContinuousMap.ext fun x =>
    Subtype.ext (ConcreteCategory.congr_hom (X.map_id n) x.1))
  map_comp φ ψ := TopCat.hom_ext (ContinuousMap.ext fun x =>
    Subtype.ext (Functor.map_comp_apply X φ ψ x.1))

/-- The underlying point of `X_n` of a point of the degree-`n` space of `X ×_Y V`. -/
abbrev fibrePt {n : SimplexCategoryᵒᵖ} (x : (fibreSpace X Y a V).obj n) : X.obj n :=
  (x : ↥(fibreOpens X Y a V n)).1

/-- A point of `X_n` lying in `a_n⁻¹(V)`, as a point of the degree-`n` space of `X ×_Y V`. -/
abbrev fibreMk {n : SimplexCategoryᵒᵖ} (y : X.obj n) (h : y ∈ fibreOpens X Y a V n) :
    (fibreSpace X Y a V).obj n :=
  (⟨y, h⟩ : ↥(fibreOpens X Y a V n))

/-- The underlying point of a point of `X ×_Y V` lies in `a_n⁻¹(V)`. -/
theorem fibrePt_mem {n : SimplexCategoryᵒᵖ} (x : (fibreSpace X Y a V).obj n) :
    fibrePt X Y a V x ∈ fibreOpens X Y a V n :=
  (x : ↥(fibreOpens X Y a V n)).2

/-- Taking the underlying point of `X_n` is injective on the degree-`n` space of `X ×_Y V`. -/
theorem fibrePt_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective (fibrePt X Y a V (n := n)) :=
  fun _ _ h => Subtype.ext h

/-- The structure maps of `X ×_Y V` act on underlying points as those of `X`. -/
@[simp]
theorem fibrePt_map {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (x : (fibreSpace X Y a V).obj n) :
    fibrePt X Y a V ((fibreSpace X Y a V).map φ x) = X.map φ (fibrePt X Y a V x) := rfl

/-- **The levelwise open immersion `X ×_Y V ⟶ X`.** -/
def fibreInclusion : fibreSpace X Y a V ⟶ X where
  app _ := TopCat.ofHom ⟨fibrePt X Y a V, continuous_subtype_val⟩
  naturality _ _ _ := TopCat.hom_ext (ContinuousMap.ext fun _ => rfl)

/-- The inclusion `X ×_Y V ⟶ X` sends a point to its underlying point of `X_n`. -/
@[simp]
theorem fibreInclusion_app_apply {n : SimplexCategoryᵒᵖ} (x : (fibreSpace X Y a V).obj n) :
    (fibreInclusion X Y a V).app n x = fibrePt X Y a V x := rfl

/-! ### The comparison of total sites -/

namespace Fibre

/-- The open of `X_n` underlying an open of the degree-`n` space of `X ×_Y V`. -/
def imageOpens {n : SimplexCategoryᵒᵖ} (W : Opens ((fibreSpace X Y a V).obj n)) :
    Opens (X.obj n) :=
  ⟨fibrePt X Y a V '' W.1,
    ((fibreOpens X Y a V n).isOpenEmbedding'.isOpen_iff_image_isOpen).1 W.isOpen⟩

/-- The open of the degree-`n` space of `X ×_Y V` cut out by an open of `X_n`. -/
def preimageOpens {n : SimplexCategoryᵒᵖ} (U : Opens (X.obj n)) :
    Opens ((fibreSpace X Y a V).obj n) :=
  ⟨fibrePt X Y a V ⁻¹' U.1, U.isOpen.preimage continuous_subtype_val⟩

/-- A point of `X ×_Y V` lies in the open cut out by `U` iff its underlying point lies in `U`. -/
@[simp]
theorem mem_preimageOpens {n : SimplexCategoryᵒᵖ} {U : Opens (X.obj n)}
    {x : (fibreSpace X Y a V).obj n} :
    x ∈ preimageOpens X Y a V U ↔ fibrePt X Y a V x ∈ U := Iff.rfl

/-- A point of `X_n` lies in `imageOpens W` iff it is the underlying point of a point of `W`. -/
theorem mem_imageOpens_iff {n : SimplexCategoryᵒᵖ} {W : Opens ((fibreSpace X Y a V).obj n)}
    {y : X.obj n} :
    y ∈ imageOpens X Y a V W ↔ ∃ x, x ∈ W ∧ fibrePt X Y a V x = y := Iff.rfl

/-- The underlying point of a point of `W` lies in `imageOpens W`. -/
theorem mem_imageOpens {n : SimplexCategoryᵒᵖ} {W : Opens ((fibreSpace X Y a V).obj n)}
    {x : (fibreSpace X Y a V).obj n} (h : x ∈ W) :
    fibrePt X Y a V x ∈ imageOpens X Y a V W :=
  ⟨x, h, rfl⟩

/-- The open of `X_n` underlying an open of `X ×_Y V` is contained in `a_n⁻¹(V)`. -/
theorem imageOpens_le {n : SimplexCategoryᵒᵖ} (W : Opens ((fibreSpace X Y a V).obj n)) :
    imageOpens X Y a V W ≤ fibreOpens X Y a V n := by
  rintro y ⟨x, _, rfl⟩
  exact fibrePt_mem X Y a V x

/-- Cutting out the open of `X_n` underlying an open `W` of `X ×_Y V` recovers `W`. -/
theorem preimageOpens_imageOpens {n : SimplexCategoryᵒᵖ}
    (W : Opens ((fibreSpace X Y a V).obj n)) :
    preimageOpens X Y a V (imageOpens X Y a V W) = W := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_imageOpens X Y a V hx)
  obtain ⟨z, hz, hzx⟩ := hx
  exact fibrePt_injective X Y a V n hzx ▸ hz

/-- An open `U ⊆ a_n⁻¹(V)` of `X_n` is the open underlying the open of `X ×_Y V` it cuts out. -/
theorem imageOpens_preimageOpens {n : SimplexCategoryᵒᵖ} {U : Opens (X.obj n)}
    (h : U ≤ fibreOpens X Y a V n) :
    imageOpens X Y a V (preimageOpens X Y a V U) = U := by
  refine le_antisymm (fun y hy => ?_) (fun y hy => ⟨fibreMk X Y a V y (h hy), hy, rfl⟩)
  obtain ⟨x, hx, rfl⟩ := hy
  exact hx

end Fibre

open Fibre

/-- **The comparison of the total site of `X ×_Y V` with that of `X`.** An object of the site of
`X ×_Y V` — an open of the space `a_n⁻¹(V)` — is sent to the open of `X_n` it cuts out, in the
same degree. -/
def fibreImage : SimplicialOpen (fibreSpace X Y a V) ⥤ SimplicialOpen X where
  obj W := ⟨W.degree, imageOpens X Y a V W.toOpens⟩
  map {W W'} h :=
    { base := h.base
      le := by
        rintro y ⟨x, hx, rfl⟩
        exact mem_imageOpens X Y a V
          (show (fibreSpace X Y a V).map h.base x ∈ W'.toOpens from
            SimplicialOpen.Hom.le h hx) }
  map_id _ := SimplicialOpen.Hom.ext _ _ rfl
  map_comp _ _ := SimplicialOpen.Hom.ext _ _ rfl

/-- The comparison of total sites preserves the degree of an object. -/
@[simp]
theorem fibreImage_obj_degree (W : SimplicialOpen (fibreSpace X Y a V)) :
    ((fibreImage X Y a V).obj W).degree = W.degree := rfl

/-- The comparison of total sites sends an open `W` of `X ×_Y V` to `imageOpens W`. -/
@[simp]
theorem fibreImage_obj_toOpens (W : SimplicialOpen (fibreSpace X Y a V)) :
    ((fibreImage X Y a V).obj W).toOpens = imageOpens X Y a V W.toOpens := rfl

/-- The comparison of total sites preserves the simplex map underlying an arrow. -/
@[simp]
theorem fibreImage_map_base {W W' : SimplicialOpen (fibreSpace X Y a V)} (h : W ⟶ W') :
    ((fibreImage X Y a V).map h).base = h.base := rfl

/-- **The comparison of total sites is fully faithful.** -/
def fibreImage_fullyFaithful : (fibreImage X Y a V).FullyFaithful where
  preimage {W W'} g :=
    { base := g.base
      le := by
        intro x hx
        obtain ⟨z, hz, hzx⟩ :=
          SimplicialOpen.Hom.le g (mem_imageOpens X Y a V (W := W.toOpens) hx)
        have hxz : (fibreSpace X Y a V).map g.base x = z :=
          (fibrePt_injective X Y a V W'.degree hzx).symm
        change (fibreSpace X Y a V).map g.base x ∈ W'.toOpens
        rw [hxz]
        exact hz }
  map_preimage _ := SimplicialOpen.Hom.ext _ _ rfl
  preimage_map _ := SimplicialOpen.Hom.ext _ _ rfl

/-- The comparison of total sites is full. -/
instance fibreImage_full : (fibreImage X Y a V).Full :=
  (fibreImage_fullyFaithful X Y a V).full

/-- The comparison of total sites is faithful. -/
instance fibreImage_faithful : (fibreImage X Y a V).Faithful :=
  (fibreImage_fullyFaithful X Y a V).faithful

/-- An object of the site of `X` that admits an arrow into an object of the fibre lies over
`a_n⁻¹(V)`: this is the universal property of the fibre product, read on opens. -/
theorem le_fibreOpens_of_hom {U : SimplicialOpen X}
    {W : SimplicialOpen (fibreSpace X Y a V)} (g : U ⟶ (fibreImage X Y a V).obj W) :
    U.toOpens ≤ fibreOpens X Y a V U.degree := by
  intro x hx
  have h1 : X.map g.base x ∈ fibreOpens X Y a V W.degree :=
    imageOpens_le X Y a V W.toOpens (SimplicialOpen.Hom.le g hx)
  change a.app U.degree x ∈ V
  rw [← augmentation_app_map_apply X Y a g.base]
  exact h1

/-- An object of the site of `X` lying over `a_n⁻¹(V)` is the image of an object of the site of
`X ×_Y V`, on the nose. -/
theorem fibreImage_obj_eq_of_le {U : SimplicialOpen X}
    (h : U.toOpens ≤ fibreOpens X Y a V U.degree) :
    (fibreImage X Y a V).obj ⟨U.degree, preimageOpens X Y a V U.toOpens⟩ = U := by
  obtain ⟨n, Uo⟩ := U
  exact congrArg (SimplicialOpen.mk n) (imageOpens_preimageOpens X Y a V h)

/-- **The comparison of total sites is downwards closed.** Every object of the site of `X`
admitting an arrow into the image of the comparison is itself in that image. -/
def fibreImage_downwardsClosed {W : SimplicialOpen (fibreSpace X Y a V)} {U : SimplicialOpen X}
    (g : U ⟶ (fibreImage X Y a V).obj W) :
    Σ W' : SimplicialOpen (fibreSpace X Y a V), (fibreImage X Y a V).obj W' ≅ U :=
  ⟨⟨U.degree, preimageOpens X Y a V U.toOpens⟩,
    eqToIso (fibreImage_obj_eq_of_le X Y a V (le_fibreOpens_of_hom X Y a V g))⟩

/-- The comparison of total sites preserves the property of an arrow of being levelwise. -/
theorem isLevelwise_fibreImage_map {W W' : SimplicialOpen (fibreSpace X Y a V)} {h : W ⟶ W'}
    (hh : SimplicialOpen.IsLevelwise h) :
    SimplicialOpen.IsLevelwise ((fibreImage X Y a V).map h) := by
  obtain ⟨e, he⟩ := hh
  exact ⟨e, he⟩

/-- **The comparison of total sites carries covering sieves to covering sieves.** -/
theorem fibreImage_coverPreserving :
    CoverPreserving (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V))
      (SimplicialOpen.grothendieckTopology X) (fibreImage X Y a V) where
  cover_preserve {W S} hS := by
    rw [SimplicialOpen.mem_grothendieckTopology] at hS ⊢
    obtain ⟨R, hR, hRS⟩ := hS
    refine ⟨R.map (fibreImage X Y a V), ⟨?_, ?_⟩, ?_⟩
    · intro U f hf
      cases hf with
      | of hf => exact isLevelwise_fibreImage_map X Y a V (hR.1 _ _ hf)
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨W', f, hf, z, hz, hzx⟩ := hR.2 x hx
      refine ⟨(fibreImage X Y a V).obj W', (fibreImage X Y a V).map f, .of hf,
        fibrePt X Y a V z, mem_imageOpens X Y a V hz, ?_⟩
      exact congrArg (fibrePt X Y a V) hzx
    · exact (R.map_le_functorPushforward (fibreImage X Y a V)).trans
        (Presieve.functorPushforward_monotone hRS)

/-- **The comparison of total sites is a continuous functor of sites.** It is cover preserving,
and it is compatible preserving because it is fully faithful and downwards closed. -/
instance fibreImage_isContinuous :
    (fibreImage X Y a V).IsContinuous
      (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V))
      (SimplicialOpen.grothendieckTopology X) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed _ (fibreImage X Y a V)
      (fun g => fibreImage_downwardsClosed X Y a V g))
    (fibreImage_coverPreserving X Y a V)

end Stacks.Topology.Simplicial

end
