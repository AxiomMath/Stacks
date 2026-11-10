module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsExistence

/-!
# Extending functors from a full subcategory of schemes: the extension is a sheaf

This is the first part of `StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf`;
it contains the open subobjects of objects of `Sch/S` and their identifications with objects
of the subcategory, and condition (a) for a covering by affine opens
(`existsUnique_glue_of_isZariskiSheafOnSubcategory`). The later parts are
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf.Presentations`,
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf.AffineSheaf` and
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf.ZariskiSheaf`.

Let `S` be a scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2)
of Stacks 0EUW, and let `F : 𝒞ᵒᵖ ⥤ Set` satisfy conditions (a) and (b). The extension
`F' = AlgebraicGeometry.ExtendingFunctors.extension` of `F` to `Sch/S` is constructed in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsExistence` as

`F'(X) = lim_{V → X, V ∈ Aff} colim_{V → V', V' ∈ 𝒞_lfp} F(V')`,

where `Aff` is the subcategory of affine objects lying over an affine open of `S` and `𝒞_lfp` is
the part of `𝒞` locally of finite presentation over `S`. This file proves that `F'` is a Zariski
sheaf on `Sch/S`, which is the analogue of condition (a) for the extension.

## The two steps

The inner colimit `G = colim_{V → V'} F(V')` satisfies the sheaf condition for a finite covering
of an object `V` of `Aff` by affine opens: writing `V = lim_l V_l` as a directed inverse limit of
objects of `𝒞_lfp`, a finite affine open covering of `V` already comes from a finite stage by
Stacks 01Z4, at that stage condition (a) applies to it, and the sheaf condition passes to the
colimit because a directed colimit of sets commutes with finite limits. This is
`isSheafForOpens_affineExtension`.

The outer limit then makes `F'` a Zariski sheaf: for an open covering `{V i}` of `X` and an
object `W` of `Aff` mapping to `X`, the inverse images of the `V i` are covered by finitely many
affine opens of `W`, each of which maps into a single `V i`, and the sections of the `F'(V i)`
over those affine opens glue by the previous paragraph. This is `isZariskiSheaf_extension`.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.IsSheafForOpens`: the sheaf condition for one covering of
  an object of `Sch/S` by open subobjects.
* `AlgebraicGeometry.ExtendingFunctors.affineExtensionι`: the leg of the colimit computing the
  extension on affine objects at an arrow into the locally-finitely-presented part.
* `AlgebraicGeometry.ExtendingFunctors.extensionπ`,
  `AlgebraicGeometry.ExtendingFunctors.extensionMk`: the projections of the limit computing the
  extension, and the section of that limit attached to a compatible family.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.existsUnique_glue_of_isZariskiSheafOnSubcategory`:
  condition (a) in the form in which it is used, namely for a covering of an object of the
  subcategory by its affine opens, the pairwise intersections being identified with objects of
  the subcategory by condition (1).
* `AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation_covering`: a finite covering of an
  affine object over an affine open of `S` by affine opens comes from the least stage of a
  presentation of that object. This is where Stacks 01Z4 enters.
* `AlgebraicGeometry.ExtendingFunctors.exists_openPresentation`: the open subobjects of the
  stages of a presentation over an affine open of the least stage form a presentation of the
  corresponding open subobject of the limit, together with a morphism of inverse systems.
* `AlgebraicGeometry.ExtendingFunctors.isSheafForOpens_affineExtension`: the sheaf condition for
  the colimit formula on a finite covering of an affine object by affine opens.
* `AlgebraicGeometry.ExtendingFunctors.affineExtension_ext`: its separatedness half, in the form
  used repeatedly afterwards.
* `AlgebraicGeometry.ExtendingFunctors.isZariskiSheaf_extension`: the analogue of condition (a)
  for the extension.

## Implementation notes

Coverings are indexed by types in the universe `u` of the schemes; a finite covering is one whose
index type is `Finite`. The index of a presentation is a poset with a least element,
obtained from an arbitrary directed presentation by restricting to the up-set of one index
(`iciIncl`, `isLimitWhiskerIciIncl`); the least element is what lets the opens of the stages be
described as the inverse images of a single open (`openAt`), matching Mathlib's
`AlgebraicGeometry.opensDiagram`, whose index category is identified with the opposite of that
poset by `botToOver`.

Condition (1) produces the objects of the subcategory isomorphic to the affine opens of its
objects only up to isomorphism, so the morphisms of the subcategory attached to an inclusion of
opens carry the chosen isomorphisms with them (`openSubHom`, `openLEHom` and their analogues
`lfpOpenSubHom`, `lfpOpenLEHom` in the locally-finitely-presented part); all the comparisons
between such morphisms are obtained by cancelling the monomorphism underlying the inclusion of
an open subobject (`eq_of_comp_overOpenι`, `eq_of_comp_openSub_eq`, `lfp_eq_of_comp_eq`).

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ExtendingFunctors

universe v w u

variable {S : Scheme.{u}}

/-! ### Open subobjects and isomorphisms -/

/-- An open immersion with a two-sided inverse carries an open to its preimage under the
inverse. -/
lemma image_eq_preimage_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    [IsOpenImmersion f] (hfg : f ≫ g = 𝟙 X) (hgf : g ≫ f = 𝟙 Y) (U : X.Opens) :
    f ''ᵁ U = g ⁻¹ᵁ U := by
  apply TopologicalSpace.Opens.ext
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    change g.base (f.base x) ∈ U
    rwa [← Scheme.Hom.comp_apply, hfg]
  · intro y hy
    refine ⟨g.base y, hy, ?_⟩
    change f.base (g.base y) = y
    rw [← Scheme.Hom.comp_apply, hgf]
    rfl

/-- Two equal open immersions have the same range. -/
lemma opensRange_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) : f.opensRange = g.opensRange := by
  subst h; rfl

/-- The inclusion of an open subobject is an open immersion on underlying schemes. -/
instance {X : Over S} (V : X.left.Opens) : IsOpenImmersion (overOpenι X V).left := by
  rw [overOpenι_left]; infer_instance

/-- The inclusion of open subobjects attached to `V ≤ W` is an open immersion on underlying
schemes. -/
instance {X : Over S} {V W : X.left.Opens} (h : V ≤ W) : IsOpenImmersion (overOpenLE X h).left := by
  rw [overOpenLE_left]; infer_instance

/-- An isomorphism of objects of `Sch/S` is an isomorphism on underlying schemes. -/
instance isIso_left_of_isIso {X Y : Over S} (f : X ⟶ Y) [IsIso f] : IsIso f.left :=
  inferInstanceAs (IsIso ((Over.forget S).map f))

/-- For an isomorphism `e` of `Sch/S`, `e.hom.left ≫ e.inv.left` is the identity. -/
@[reassoc (attr := simp)]
lemma hom_left_comp_inv_left {X Y : Over S} (e : X ≅ Y) : e.hom.left ≫ e.inv.left = 𝟙 _ := by
  rw [← Over.comp_left, e.hom_inv_id, Over.id_left]

/-- For an isomorphism `e` of `Sch/S`, `e.inv.left ≫ e.hom.left` is the identity. -/
@[reassoc (attr := simp)]
lemma inv_left_comp_hom_left {X Y : Over S} (e : X ≅ Y) : e.inv.left ≫ e.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, e.inv_hom_id, Over.id_left]

/-- The image of an open under an isomorphism of `Sch/S` is its preimage under the inverse. -/
lemma image_left_eq_preimage_inv_left {X Y : Over S} (e : X ≅ Y) (U : X.left.Opens) :
    e.hom.left ''ᵁ U = e.inv.left ⁻¹ᵁ U :=
  image_eq_preimage_of_isIso _ _ (hom_left_comp_inv_left e) (inv_left_comp_hom_left e) U

/-! ### Open subobjects and morphisms into them -/

/-- The morphism of open subobjects induced by a morphism carrying one open into another. -/
noncomputable def overOpenResLE {X Y : Over S} (f : Y ⟶ X) {V : X.left.Opens} {W : Y.left.Opens}
    (h : W ≤ f.left ⁻¹ᵁ V) : overOpen Y W ⟶ overOpen X V :=
  Over.homMk (f.left.resLE V W h) (by
    change f.left.resLE V W h ≫ V.ι ≫ X.hom = W.ι ≫ Y.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w f])

/-- The underlying morphism of schemes of `overOpenResLE f h` is `f.left.resLE V W h`. -/
@[simp]
lemma overOpenResLE_left {X Y : Over S} (f : Y ⟶ X) {V : X.left.Opens} {W : Y.left.Opens}
    (h : W ≤ f.left ⁻¹ᵁ V) : (overOpenResLE f h).left = f.left.resLE V W h := rfl

/-- The morphism `overOpenResLE f h` followed by the inclusion of `V` is the inclusion of `W`
followed by `f`. -/
lemma overOpenResLE_comp_overOpenι {X Y : Over S} (f : Y ⟶ X) {V : X.left.Opens}
    {W : Y.left.Opens} (h : W ≤ f.left ⁻¹ᵁ V) :
    overOpenResLE f h ≫ overOpenι X V = overOpenι Y W ≫ f := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, Over.comp_left, overOpenResLE_left, overOpenι_left, overOpenι_left]
  exact Scheme.Hom.resLE_comp_ι _ _

/-- Two morphisms into an open subobject agree as soon as they do after composition with the
inclusion of that open subobject. -/
lemma eq_of_comp_overOpenι {Y X : Over S} {V : X.left.Opens} {a b : Y ⟶ overOpen X V}
    (h : a ≫ overOpenι X V = b ≫ overOpenι X V) : a = b := by
  refine Over.OverMorphism.ext ?_
  have h1 : a.left ≫ V.ι = b.left ≫ V.ι := by
    have := congrArg Over.Hom.left h
    simpa only [Over.comp_left, overOpenι_left] using this
  exact (cancel_mono V.ι).mp h1

/-- A morphism of `Sch/S` whose image lies in an open subobject factors through it. -/
noncomputable def liftOverOpen {Z X : Over S} (g : Z ⟶ X) (V : X.left.Opens)
    (h : Set.range (⇑g.left) ⊆ (V : Set X.left)) : Z ⟶ overOpen X V :=
  Over.homMk (IsOpenImmersion.lift V.ι g.left (by rwa [Scheme.Opens.range_ι])) (by
    change IsOpenImmersion.lift V.ι g.left _ ≫ V.ι ≫ X.hom = Z.hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w g])

/-- The factorisation `liftOverOpen g V h` followed by the inclusion of `V` is `g`. -/
@[simp]
lemma liftOverOpen_comp_overOpenι {Z X : Over S} (g : Z ⟶ X) (V : X.left.Opens)
    (h : Set.range (⇑g.left) ⊆ (V : Set X.left)) :
    liftOverOpen g V h ≫ overOpenι X V = g := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, overOpenι_left]
  exact IsOpenImmersion.lift_fac _ _ _

/-- An affine open of an affine object of `Sch/S` lying over an affine open of `S` is again such
an object. -/
lemma isAffineOverAffineOpen_overOpen {W : Over S} (hW : IsAffineOverAffineOpen W)
    {W' : W.left.Opens} (hW' : IsAffineOpen W') :
    IsAffineOverAffineOpen (overOpen W W') := by
  obtain ⟨-, U, g, hg⟩ := hW
  exact ⟨hW', U, W'.ι ≫ g, by rw [Category.assoc, hg]; rfl⟩

/-- **A finite affine refinement of an open covering of a quasi-compact scheme.** -/
lemma exists_finite_affine_refinement {Y : Scheme.{u}} [CompactSpace Y] {ι : Type u}
    (V : ι → Y.Opens) (hV : ⨆ i, V i = ⊤) :
    ∃ (κ : Type u) (_ : Finite κ) (U : κ → Y.Opens) (c : κ → ι),
      (∀ a, IsAffineOpen (U a)) ∧ (∀ a, U a ≤ V (c a)) ∧ ⨆ a, U a = ⊤ := by
  classical
  have hbas : ∀ y : Y, ∃ (i : ι) (O : Y.Opens), IsAffineOpen O ∧ y ∈ O ∧ O ≤ V i := by
    intro y
    have hy : y ∈ (⨆ i, V i) := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    obtain ⟨O, hO, hyO, hOV⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hi
    exact ⟨i, O, hO, hyO, hOV⟩
  choose iy Oy hOyaff hyOy hOyV using hbas
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : Y => (Oy y : Set Y))
    (fun y => (Oy y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyOy y⟩)
  refine ⟨(t : Type u), inferInstance, fun a => Oy a.1, fun a => iy a.1,
    fun a => hOyaff a.1, fun a => hOyV a.1, ?_⟩
  refine le_antisymm le_top (fun y _ => ?_)
  obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hya⟩


/-! ### Condition (a) for a covering by affine opens -/

variable {P : ObjectProperty (Over S)}

/-- The morphism of the full subcategory attached to an identification of an open subobject of an
object of the subcategory with an object of the subcategory. -/
def openSubHom {Z : Over S} (hZ : P Z) {V : Z.left.Opens} {A : P.FullSubcategory}
    (e : overOpen Z V ≅ A.obj) : A ⟶ (⟨Z, hZ⟩ : P.FullSubcategory) :=
  ObjectProperty.homMk (e.inv ≫ overOpenι Z V)

/-- The morphism of the full subcategory attached to an inclusion `V' ≤ V` of opens of an object
of `Sch/S` and identifications of the two open subobjects with objects of the subcategory. -/
noncomputable def openLEHom {Z : Over S} {V V' : Z.left.Opens} (h : V' ≤ V)
    {A A' : P.FullSubcategory} (e : overOpen Z V ≅ A.obj) (e' : overOpen Z V' ≅ A'.obj) : A' ⟶ A :=
  ObjectProperty.homMk (e'.inv ≫ overOpenLE Z h ≫ e.hom)

/-- In `Sch/S`, `openSubHom hZ e` is `e.inv` followed by the inclusion of `V`. -/
@[simp]
lemma ι_map_openSubHom {Z : Over S} (hZ : P Z) {V : Z.left.Opens} {A : P.FullSubcategory}
    (e : overOpen Z V ≅ A.obj) :
    P.ι.map (openSubHom hZ e) = e.inv ≫ overOpenι Z V :=
  rfl

/-- In `Sch/S`, `openLEHom h e e'` is `e'.inv`, followed by the inclusion `V' ≤ V`, followed by
`e.hom`. -/
@[simp]
lemma ι_map_openLEHom {Z : Over S} {V V' : Z.left.Opens} (h : V' ≤ V) {A A' : P.FullSubcategory}
    (e : overOpen Z V ≅ A.obj) (e' : overOpen Z V' ≅ A'.obj) :
    P.ι.map (openLEHom h e e') = e'.inv ≫ overOpenLE Z h ≫ e.hom :=
  rfl

/-- The underlying morphism of schemes of `openSubHom hZ e` is `e.inv.left ≫ V.ι`. -/
lemma left_openSubHom {Z : Over S} (hZ : P Z) {V : Z.left.Opens} {A : P.FullSubcategory}
    (e : overOpen Z V ≅ A.obj) :
    (P.ι.map (openSubHom hZ e)).left = e.inv.left ≫ V.ι := by
  rw [ι_map_openSubHom, Over.comp_left, overOpenι_left]

/-- The underlying morphism of schemes of `openLEHom h e e'` is
`e'.inv.left ≫ Z.left.homOfLE h ≫ e.hom.left`. -/
lemma left_openLEHom {Z : Over S} {V V' : Z.left.Opens} (h : V' ≤ V) {A A' : P.FullSubcategory}
    (e : overOpen Z V ≅ A.obj) (e' : overOpen Z V' ≅ A'.obj) :
    (P.ι.map (openLEHom h e e')).left = e'.inv.left ≫ Z.left.homOfLE h ≫ e.hom.left := by
  rw [ι_map_openLEHom, Over.comp_left, Over.comp_left, overOpenLE_left]

/-- The morphism `openLEHom h e e'` followed by `openSubHom hZ e` is `openSubHom hZ e'`. -/
lemma openLEHom_comp_openSubHom {Z : Over S} (hZ : P Z) {V V' : Z.left.Opens} (h : V' ≤ V)
    {A A' : P.FullSubcategory} (e : overOpen Z V ≅ A.obj) (e' : overOpen Z V' ≅ A'.obj) :
    openLEHom h e e' ≫ openSubHom hZ e = openSubHom hZ e' := by
  refine P.ι.map_injective (Over.OverMorphism.ext ?_)
  rw [Functor.map_comp, Over.comp_left, left_openLEHom, left_openSubHom, left_openSubHom,
    Category.assoc, Category.assoc, hom_left_comp_inv_left_assoc]
  simp

/-- The underlying morphism of schemes of `openSubHom hZ e` is an open immersion. -/
instance isOpenImmersion_left_openSubHom {Z : Over S} (hZ : P Z) {V : Z.left.Opens}
    {A : P.FullSubcategory} (e : overOpen Z V ≅ A.obj) :
    IsOpenImmersion (P.ι.map (openSubHom hZ e)).left := by
  rw [left_openSubHom]; infer_instance

/-- The underlying morphism of schemes of `openLEHom h e e'` is an open immersion. -/
instance isOpenImmersion_left_openLEHom {Z : Over S} {V V' : Z.left.Opens} (h : V' ≤ V)
    {A A' : P.FullSubcategory} (e : overOpen Z V ≅ A.obj) (e' : overOpen Z V' ≅ A'.obj) :
    IsOpenImmersion (P.ι.map (openLEHom h e e')).left := by
  rw [left_openLEHom]; infer_instance

/-- The range of the underlying morphism of schemes of `openSubHom hZ e` is `V`. -/
@[simp]
lemma opensRange_left_openSubHom {Z : Over S} (hZ : P Z) {V : Z.left.Opens}
    {A : P.FullSubcategory} (e : overOpen Z V ≅ A.obj) :
    (P.ι.map (openSubHom hZ e)).left.opensRange = V := by
  rw [opensRange_congr (left_openSubHom hZ e), Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

/-- The range of the underlying morphism of schemes of `openLEHom h e e'` is the inverse image
of `V'` under `e.inv.left ≫ V.ι`. -/
lemma opensRange_left_openLEHom {Z : Over S} {V V' : Z.left.Opens} (h : V' ≤ V)
    {A A' : P.FullSubcategory} (e : overOpen Z V ≅ A.obj) (e' : overOpen Z V' ≅ A'.obj) :
    (P.ι.map (openLEHom h e e')).left.opensRange = e.inv.left ⁻¹ᵁ (V.ι ⁻¹ᵁ V') := by
  rw [opensRange_congr (left_openLEHom h e e'), Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_comp, Scheme.opensRange_homOfLE, image_left_eq_preimage_inv_left]

/-- **Condition (a) of Stacks 0EUW, for a covering of an object of the full subcategory by its
affine opens.** The subcategory contains, up to isomorphism, every affine open of one of its
objects; a covering `Z = ⋃ V i` by such opens, with the pairwise intersections again identified
with objects of the subcategory, is a Zariski covering in the sense of condition (a), its
footnote being satisfied by the one-element coverings of the intersections. So a family of
sections over the `V i` agreeing on the intersections glues uniquely. -/
theorem existsUnique_glue_of_isZariskiSheafOnSubcategory {F : P.FullSubcategoryᵒᵖ ⥤ Type w}
    (haF : IsZariskiSheafOnSubcategory P F) {Z : Over S} (hZ : P Z) {ι : Type u}
    {V : ι → Z.left.Opens} (hV : ⨆ i, V i = ⊤) {A : ι → P.FullSubcategory}
    (e : ∀ i, overOpen Z (V i) ≅ (A i).obj) {V₂ : ι → ι → Z.left.Opens}
    {A₂ : ι → ι → P.FullSubcategory} (e₂ : ∀ i j, overOpen Z (V₂ i j) ≅ (A₂ i j).obj)
    (h₁ : ∀ i j, V₂ i j ≤ V i) (h₂ : ∀ i j, V₂ i j ≤ V j)
    (h₃ : ∀ i j, (V i).ι ⁻¹ᵁ V₂ i j = (V i).ι ⁻¹ᵁ V j)
    (s : ∀ i, F.obj (op (A i)))
    (hs : ∀ i j, F.map (openLEHom (h₁ i j) (e i) (e₂ i j)).op (s i)
      = F.map (openLEHom (h₂ i j) (e j) (e₂ i j)).op (s j)) :
    ∃! t : F.obj (op (⟨Z, hZ⟩ : P.FullSubcategory)),
      ∀ i, F.map (openSubHom hZ (e i)).op t = s i := by
  refine haF ⟨Z, hZ⟩ ι A (fun i => openSubHom hZ (e i)) inferInstance ?_
    (fun _ _ => PUnit.{u + 1}) (fun i j _ => A₂ i j)
    (fun i j _ => openLEHom (h₁ i j) (e i) (e₂ i j))
    (fun i j _ => openLEHom (h₂ i j) (e j) (e₂ i j)) inferInstance ?_ ?_ s ?_
  · simp only [opensRange_left_openSubHom]
    exact hV
  · intro i j _
    rw [openLEHom_comp_openSubHom, openLEHom_comp_openSubHom]
  · intro i j
    simp only [iSup_const, opensRange_left_openLEHom, opensRange_left_openSubHom,
      left_openSubHom hZ (e i), Scheme.Hom.comp_preimage, h₃]
  · intro i j _
    exact hs i j

end AlgebraicGeometry.ExtendingFunctors

end
