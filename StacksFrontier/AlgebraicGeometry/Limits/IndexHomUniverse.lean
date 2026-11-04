module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative

/-!
# Cofiltered limits of schemes at an unrestricted index morphism universe

`Mathlib.AlgebraicGeometry.AffineTransitionLimit` develops inverse limits of schemes with affine
transition morphisms for an index category `I : Type u` with `[Category.{u} I]`, where `u` is the
universe of the schemes. A statement whose index category has morphisms in a universe `v`
independent of `u` therefore cannot invoke those results, and the existing workarounds add a
smallness hypothesis on the hom types (`CategoryTheory.LocallySmall.{u} I`, or the
`CategoryTheory.EssentiallySmall.{u} I` of
`AlgebraicGeometry.exists_morphism_after_baseChange`) which such a statement does not have.

No hypothesis is needed. A diagram of schemes only ever uses the *images* of the index morphisms,
and those are morphisms of schemes, hence already live in the scheme universe. This file makes
that precise: `CategoryTheory.Functor.FullImage D` is the category with the same objects as `I`
and with the morphisms of the target category that lie in the image of `D`. Its hom types are
subtypes of hom types of the target, so it is locally `u`-small whatever `v` was, and `D` factors
through it by a functor that is full and bijective on objects. Cones and limit cones transport
both ways, so Mathlib's results apply to the factored diagram and their conclusions — all of the
form "there is an index `j` and a morphism `j ⟶ i` such that …", the conclusion depending on the
index morphism only through its image under `D` — are pulled back along the factorization.

## Main definitions

* `CategoryTheory.Functor.FullImage`: the full image of a functor, with its category structure.
* `CategoryTheory.Functor.FullImage.ι`: the projection of the full image to the target category.
* `CategoryTheory.Functor.FullImage.toFullImage`: the factorization of `D` through its full image.
* `CategoryTheory.Functor.FullImage.cone` and `CategoryTheory.Functor.FullImage.coneOfι`:
  the two directions of the correspondence between cones over `D` and cones over `ι D`.

## Main results

* `CategoryTheory.Functor.FullImage.isLimitCone`: a limit cone over `D` is a limit cone over
  `ι D`.
* `CategoryTheory.Functor.FullImage.instLocallySmall` and the `CategoryTheory.InitiallySmall`
  instances: the full image is always locally `u`-small, and it is initially (resp. essentially)
  `u`-small as soon as `I` is initially (resp. objectwise) `u`-small. So a diagram landing in a
  locally `u`-small category never needs `CategoryTheory.LocallySmall.{u} I`, which is one of the
  two halves of `CategoryTheory.EssentiallySmall.{u} I`; only the smallness of the *objects* of
  the index category is a genuine hypothesis.
* The following are Mathlib's results of the same name with the index morphism universe freed,
  stated for `I : Type u` with `[Category.{v} I]` and no smallness hypothesis:
  `AlgebraicGeometry.isAffineHom_π_app'`,
  `AlgebraicGeometry.Scheme.compactSpace_of_isLimit'`,
  `AlgebraicGeometry.Scheme.nonempty_of_isLimit'` (Tag 01Z2),
  `AlgebraicGeometry.exists_map_eq_top'`,
  `AlgebraicGeometry.exists_app_map_eq_zero_of_isLimit'`,
  `AlgebraicGeometry.exists_app_map_eq_map_of_isLimit'`,
  `AlgebraicGeometry.exists_appTop_map_eq_zero_of_isLimit'`,
  `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit'`,
  `AlgebraicGeometry.exists_preimage_eq'` and
  `AlgebraicGeometry.exists_isAffineOpen_preimage_eq'` (Tag 01Z4 (1)),
  `AlgebraicGeometry.exists_map_preimage_eq_map_preimage'` (Tag 01Z4 (2)),
  `AlgebraicGeometry.isBasis_preimage_isAffineOpen'`,
  `AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit'` (Tag 01Z5),
  `AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit'` (Tag 01Z6),
  `AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine_of_finite'`.
* `AlgebraicGeometry.exists_morphism_after_baseChange'` and
  `AlgebraicGeometry.eventually_eq_of_baseChange_eq'` are Tag 01ZM (2) and (3) with the
  `CategoryTheory.EssentiallySmall.{u}` hypothesis of
  `AlgebraicGeometry.exists_morphism_after_baseChange` removed.
* `AlgebraicGeometry.isAffineHom_π_app_of_initiallySmall'` and
  `AlgebraicGeometry.exists_isAffineOpen_preimage_eq_of_initiallySmall'` are the two results of
  `StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit` of the same name with
  the `CategoryTheory.LocallySmall.{u}` hypothesis dropped, for an index category whose objects
  live anywhere. They are examples of the recipe: every result in that file applies to `ι D`,
  `FullImage.cone D c` and `FullImage.isLimitCone D hc` under `CategoryTheory.InitiallySmall.{u} I`
  alone, because the full image carries local smallness for free.

## Implementation notes

`FullImage D` is a structure wrapping an index rather than a type synonym for `I`, so that its
category structure cannot be confused with that of `I`.

Its hom type is `{g : D.obj j ⟶ D.obj k // ∃ f : j ⟶ k, D.map f = g}`. Taking the subtype of
morphisms *in the image* rather than a quotient of `j ⟶ k` is what makes the composition and the
cone condition well defined without choosing a representative: a morphism of `FullImage D` already
*is* the morphism of schemes it is to be sent to. Choice is used once, in pulling a conclusion
back: `CategoryTheory.Functor.FullImage.hom` picks an index morphism whose image is a given
morphism of the full image, and since the conclusions being transported depend on the index
morphism only through its image, rewriting along
`CategoryTheory.Functor.FullImage.map_hom` carries them over.

What this frees is the *morphism* universe only, and that is the whole scope of the file. The
smallness of the *objects* of the index category is a genuine hypothesis in this family and is
not touched here: `CategoryTheory.not_initiallySmall_op_ordinal`
(`StacksFrontier/AlgebraicGeometry/EventualFiniteness/Basic.lean`) exhibits a directed preorder
in `Type (u+1)` with no `u`-small cofinal part. So a statement about `D : I ⥤ Scheme.{u}` with
`I : Type u` needs nothing, while one with `I : Type uI` for an unrelated `uI` still needs
`CategoryTheory.Small.{u} I` or `CategoryTheory.InitiallySmall.{u} I` — but, by the instances
above, never `CategoryTheory.LocallySmall.{u} I` on top of it.

`FullImage D` is cofiltered when `I` is. Cofilteredness of the morphism condition is where
cofilteredness of `I` is genuinely used: two morphisms of `FullImage D` are images of two index
morphisms, which are equalized after precomposition in `I`, and the images of the equalized
composites are equal because they are equal as morphisms of schemes.

## References

* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

universe w v uI u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {I : Type uI} [Category.{v} I] {C : Type w} [Category.{u} C] (D : I ⥤ C)

/-- The full image of a functor `D : I ⥤ C`: the objects are those of `I`, and the morphisms are
the morphisms of `C` lying in the image of `D`. -/
public structure FullImage (D : I ⥤ C) where
  /-- The index of `I` underlying an object of the full image. -/
  as : I

namespace FullImage

/-- The category structure on the full image: a morphism `j ⟶ k` is a morphism
`D.obj j.as ⟶ D.obj k.as` of `C` in the image of `D`, with the composition and identities
of `C`. -/
public instance : Category.{u} (FullImage D) where
  Hom j k := {g : D.obj j.as ⟶ D.obj k.as // ∃ f : j.as ⟶ k.as, D.map f = g}
  id j := ⟨𝟙 (D.obj j.as), 𝟙 j.as, D.map_id _⟩
  comp {_ _ _} g h := ⟨g.1 ≫ h.1, by
    obtain ⟨f, hf⟩ := g.2
    obtain ⟨f', hf'⟩ := h.2
    exact ⟨f ≫ f', by rw [D.map_comp, hf, hf']⟩⟩

/-- Two morphisms of the full image are equal as soon as their underlying morphisms of `C` are. -/
@[ext]
public lemma hom_ext {j k : FullImage D} {g h : j ⟶ k} (H : g.1 = h.1) : g = h := Subtype.ext H

/-- The underlying morphism of `C` of an identity of the full image is the identity. -/
@[simp]
public lemma id_val (j : FullImage D) : (𝟙 j : j ⟶ j).1 = 𝟙 (D.obj j.as) := rfl

/-- The underlying morphism of `C` of a composite in the full image is the composite of the
underlying morphisms. -/
@[simp]
public lemma comp_val {j k l : FullImage D} (g : j ⟶ k) (h : k ⟶ l) :
    (g ≫ h).1 = g.1 ≫ h.1 := rfl

/-- The projection of the full image of `D` to the target category. -/
@[simps]
public def ι : FullImage D ⥤ C where
  obj j := D.obj j.as
  map g := g.1

/-- The factorization of `D` through its full image. -/
@[simps]
public def toFullImage : I ⥤ FullImage D where
  obj j := ⟨j⟩
  map f := ⟨D.map f, f, rfl⟩

/-- `D` is the factorization through its full image followed by the projection. -/
public lemma toFullImage_comp_ι : toFullImage D ⋙ ι D = D := rfl

/-- A choice of index morphism realizing a morphism of the full image of `D`. -/
public noncomputable def hom {j k : FullImage D} (g : j ⟶ k) : j.as ⟶ k.as := g.2.choose

/-- The index morphism `hom D g` is sent by `D` to the morphism of `C` underlying `g`. -/
public lemma map_hom {j k : FullImage D} (g : j ⟶ k) : D.map (hom D g) = (ι D).map g :=
  g.2.choose_spec

/-- The factorization of `D` through its full image is full: a morphism of the full image is by
definition the image of an index morphism. -/
public instance : (toFullImage D).Full where
  map_surjective g := ⟨g.2.choose, hom_ext D g.2.choose_spec⟩

/-- The projection of the full image of `D` to the target category is faithful. -/
public instance : (ι D).Faithful where
  map_injective h := hom_ext D h

/-- The full image of a functor out of a cofiltered (or empty) category is cofiltered (or empty):
two parallel morphisms are images of two index morphisms, and the image of an index morphism
equalizing those equalizes them. -/
public instance [IsCofilteredOrEmpty I] : IsCofilteredOrEmpty (FullImage D) where
  cone_objs j k := by
    obtain ⟨l, f, g, -⟩ := IsCofilteredOrEmpty.cone_objs j.as k.as
    exact ⟨⟨l⟩, ⟨D.map f, f, rfl⟩, ⟨D.map g, g, rfl⟩, trivial⟩
  cone_maps j k g h := by
    obtain ⟨f, hf⟩ := g.2
    obtain ⟨f', hf'⟩ := h.2
    obtain ⟨l, e, he⟩ := IsCofilteredOrEmpty.cone_maps f f'
    refine ⟨⟨l⟩, ⟨D.map e, e, rfl⟩, hom_ext D ?_⟩
    simp only [comp_val]
    rw [← hf, ← hf', ← D.map_comp, ← D.map_comp, he]

/-- The full image of a functor out of a cofiltered category is cofiltered. -/
public instance [IsCofiltered I] : IsCofiltered (FullImage D) where
  nonempty := ⟨⟨IsCofiltered.nonempty.some⟩⟩

/-- The full image is `u`-small when `I` is, its objects being those of `I`. -/
public instance [Small.{u} I] : Small.{u} (FullImage D) :=
  small_of_injective (f := FullImage.as) (fun ⟨_⟩ ⟨_⟩ h => by simpa using h)

/-- The full image is always locally `u`-small: its hom types are subtypes of hom types of `C`. -/
public instance : LocallySmall.{u} (FullImage D) where
  hom_small _ _ := small_self _

/-- The full image is essentially `u`-small when `I` is `u`-small. -/
public instance [Small.{u} I] : EssentiallySmall.{u} (FullImage D) :=
  essentiallySmall_of_small_of_locallySmall _

/-- The factorization of `D` through its full image is an initial functor: an object of the
costructured-arrow category at `d` is an index `j` together with a morphism of the full image
`⟨j⟩ ⟶ d`, and such a morphism is by definition the image of an index morphism `j ⟶ d.as`, which
is a morphism to the costructured arrow `𝟙 d`. So every object of that category maps to a single
one, which makes it connected. -/
public instance : (toFullImage D).Initial where
  out d := by
    have hhub : ∀ x : CostructuredArrow (toFullImage D) d,
        Nonempty (x ⟶ CostructuredArrow.mk (S := toFullImage D) (T := d) (Y := d.as) (𝟙 d)) := by
      intro x
      obtain ⟨f, hf⟩ := x.hom.2
      exact ⟨CostructuredArrow.homMk f (hom_ext D ((Category.comp_id (D.map f)).trans hf))⟩
    have : Nonempty (CostructuredArrow (toFullImage D) d) :=
      ⟨CostructuredArrow.mk (S := toFullImage D) (T := d) (Y := d.as) (𝟙 d)⟩
    refine zigzag_isConnected fun x y => ?_
    exact (Zigzag.of_hom (hhub x).some).trans (Zigzag.of_inv (hhub y).some)

/-- Initial smallness of the index category transfers to its full image, where local smallness
is automatic. This is what makes `CategoryTheory.LocallySmall.{u} I` — half of
`CategoryTheory.EssentiallySmall.{u} I` — never a necessary hypothesis for a diagram landing in a
locally `u`-small category. -/
public instance [InitiallySmall.{u} I] : InitiallySmall.{u} (FullImage D) :=
  InitiallySmall.mk' (fromInitialModel.{u} I ⋙ toFullImage D)

/-- A cone over `D` is a cone over the projection of the full image of `D`. -/
@[simps]
public def cone (c : Cone D) : Cone (ι D) where
  pt := c.pt
  π :=
    { app := fun j => c.π.app j.as
      naturality := fun _ _ g => by
        obtain ⟨f, hf⟩ := g.2
        simp [ι, ← hf] }

/-- A cone over the projection of the full image of `D` is a cone over `D`. -/
@[simps]
public def coneOfι (s : Cone (ι D)) : Cone D where
  pt := s.pt
  π :=
    { app := fun j => s.π.app ⟨j⟩
      naturality := fun _ _ f => s.π.naturality ((toFullImage D).map f) }

/-- A limit cone over `D` is a limit cone over the projection of the full image of `D`. -/
public def isLimitCone {c : Cone D} (hc : IsLimit c) : IsLimit (cone D c) where
  lift s := hc.lift (coneOfι D s)
  fac s j := hc.fac (coneOfι D s) j.as
  uniq s m hm := hc.uniq (coneOfι D s) m fun j => hm ⟨j⟩

end FullImage

end CategoryTheory.Functor

namespace AlgebraicGeometry

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

/-! ### Transfer of the hypotheses of the diagram to its full image -/

section Transfer

variable {I : Type uI} [Category.{v} I] (D : I ⥤ Scheme.{u})

/-- The objects of the projection of the full image of `D` are quasi-compact when those of `D`
are. -/
public instance compactSpace_fullImage_obj [∀ i : I, CompactSpace (D.obj i)]
    (j : FullImage D) : CompactSpace ((ι D).obj j) :=
  inferInstanceAs (CompactSpace (D.obj j.as))

/-- The objects of the projection of the full image of `D` are quasi-separated when those of `D`
are. -/
public instance quasiSeparatedSpace_fullImage_obj [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (j : FullImage D) : QuasiSeparatedSpace ((ι D).obj j) :=
  inferInstanceAs (QuasiSeparatedSpace (D.obj j.as))

/-- The objects of the projection of the full image of `D` are nonempty when those of `D` are. -/
public instance nonempty_fullImage_obj [∀ i : I, Nonempty (D.obj i)]
    (j : FullImage D) : Nonempty ((ι D).obj j) :=
  inferInstanceAs (Nonempty (D.obj j.as))

/-- The morphisms of the projection of the full image of `D` are affine when the transition
morphisms of `D` are, each being the image under `D` of an index morphism. -/
public instance isAffineHom_fullImage_map [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    {j k : FullImage D} (g : j ⟶ k) : IsAffineHom ((ι D).map g) :=
  map_hom D g ▸ (inferInstance : IsAffineHom (D.map (hom D g)))

end Transfer

/-! ### Mathlib's results with the index morphism universe freed -/

variable {I : Type u} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

section

variable [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [IsCofiltered I]

include c in
/-- `AlgebraicGeometry.isAffineHom_π_app` with the index morphism universe unrestricted. -/
public lemma isAffineHom_π_app' (hc : IsLimit c) (i : I) : IsAffineHom (c.π.app i) :=
  isAffineHom_π_app (ι D) (cone D c) (isLimitCone D hc) ⟨i⟩

include c in
/-- `AlgebraicGeometry.Scheme.compactSpace_of_isLimit` with the index morphism universe
unrestricted. -/
public lemma Scheme.compactSpace_of_isLimit' (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] : CompactSpace c.pt :=
  Scheme.compactSpace_of_isLimit (ι D) (cone D c) (isLimitCone D hc)

include c in
/-- `AlgebraicGeometry.exists_map_eq_top` with the index morphism universe unrestricted. -/
public lemma exists_map_eq_top' (hc : IsLimit c) [∀ i : I, CompactSpace (D.obj i)]
    {i : I} (U : (D.obj i).Opens) (hU : c.π.app i ⁻¹ᵁ U = ⊤) :
    ∃ (j : I) (f : j ⟶ i), D.map f ⁻¹ᵁ U = ⊤ := by
  obtain ⟨j, g, hj⟩ := exists_map_eq_top (ι D) (cone D c) (isLimitCone D hc) (i := ⟨i⟩) U hU
  exact ⟨j.as, hom D g, map_hom D g ▸ hj⟩

include c in
/-- `AlgebraicGeometry.exists_app_map_eq_zero_of_isLimit` with the index morphism universe
unrestricted. -/
public lemma exists_app_map_eq_zero_of_isLimit' (hc : IsLimit c)
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (X := D.obj i) U) (s : Γ(D.obj i, U))
    (hs : (c.π.app i).app U s = 0) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).app U s = 0 := by
  obtain ⟨j, g, hj⟩ := exists_app_map_eq_zero_of_isLimit (ι D) (cone D c) (isLimitCone D hc)
    (i := ⟨i⟩) hU s hs
  exact ⟨j.as, hom D g, map_hom D g ▸ hj⟩

include c in
/-- `AlgebraicGeometry.exists_app_map_eq_map_of_isLimit` with the index morphism universe
unrestricted. -/
public lemma exists_app_map_eq_map_of_isLimit' (hc : IsLimit c)
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (X := D.obj i) U) (s t : Γ(D.obj i, U))
    (hs : (c.π.app i).app U s = (c.π.app i).app U t) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).app U s = (D.map f).app U t := by
  obtain ⟨j, g, hj⟩ := exists_app_map_eq_map_of_isLimit (ι D) (cone D c) (isLimitCone D hc)
    (i := ⟨i⟩) hU s t hs
  exact ⟨j.as, hom D g, map_hom D g ▸ hj⟩

include c in
/-- `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` with the index morphism universe
unrestricted. -/
public lemma exists_appTop_π_eq_of_isLimit' (hc : IsLimit c) (s : Γ(c.pt, ⊤))
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)] :
    ∃ (i : I) (t : Γ(D.obj i, ⊤)), s = (c.π.app i).appTop t := by
  obtain ⟨j, t, hj⟩ := exists_appTop_π_eq_of_isLimit (ι D) (cone D c) (isLimitCone D hc) s
  exact ⟨j.as, t, hj⟩

include c in
/-- `AlgebraicGeometry.exists_appTop_map_eq_zero_of_isLimit` with the index morphism universe
unrestricted. -/
public lemma exists_appTop_map_eq_zero_of_isLimit' (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] (i : I) (s : Γ(D.obj i, ⊤))
    (hs : (c.π.app i).appTop s = 0) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).appTop s = 0 := by
  obtain ⟨j, g, hj⟩ := exists_appTop_map_eq_zero_of_isLimit (ι D) (cone D c) (isLimitCone D hc)
    (i := ⟨i⟩) s hs
  exact ⟨j.as, hom D g, map_hom D g ▸ hj⟩

include c in
/-- **Stacks Project, Tag 01Z2**: `AlgebraicGeometry.Scheme.nonempty_of_isLimit` with the index
morphism universe unrestricted. -/
public lemma Scheme.nonempty_of_isLimit' (hc : IsLimit c) [∀ i : I, Nonempty (D.obj i)]
    [∀ i : I, CompactSpace (D.obj i)] : Nonempty c.pt :=
  Scheme.nonempty_of_isLimit (ι D) (cone D c) (isLimitCone D hc)

include c in
/-- **Stacks Project, Tag 01Z4 (1)**: `exists_preimage_eq` with the index morphism universe
unrestricted. -/
public lemma exists_preimage_eq' (hc : IsLimit c) (U : c.pt.Opens)
    (hU : IsCompact (U : Set c.pt)) :
    ∃ (i : I) (V : (D.obj i).Opens), IsCompact (V : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ V = U := by
  obtain ⟨j, V, hV, hj⟩ := exists_preimage_eq (ι D) (cone D c) (isLimitCone D hc) U hU
  exact ⟨j.as, V, hV, hj⟩

include c in
/-- `AlgebraicGeometry.isBasis_preimage_isAffineOpen` with the index morphism universe
unrestricted. -/
public lemma isBasis_preimage_isAffineOpen' (hc : IsLimit c) :
    TopologicalSpace.Opens.IsBasis
      { (c.π.app i ⁻¹ᵁ V : c.pt.Opens) | (i : I) (V : (D.obj i).Opens) (_ : IsAffineOpen V) } := by
  have hset : { (c.π.app i ⁻¹ᵁ V : c.pt.Opens) |
        (i : I) (V : (D.obj i).Opens) (_ : IsAffineOpen V) } =
      { ((cone D c).π.app j ⁻¹ᵁ V : (cone D c).pt.Opens) |
        (j : FullImage D) (V : ((ι D).obj j).Opens) (_ : IsAffineOpen V) } := by
    ext U
    exact ⟨fun ⟨i, V, hV, h⟩ => ⟨⟨i⟩, V, hV, h⟩, fun ⟨j, V, hV, h⟩ => ⟨j.as, V, hV, h⟩⟩
  rw [hset]
  exact isBasis_preimage_isAffineOpen (ι D) (cone D c) (isLimitCone D hc)

include c in
/-- **Stacks Project, Tag 01Z5**: `AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit` with
the index morphism universe unrestricted. -/
public lemma Scheme.exists_isQuasiAffine_of_isLimit' (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [IsQuasiAffine c.pt] : ∃ i : I, IsQuasiAffine (D.obj i) := by
  have : IsQuasiAffine (cone D c).pt := inferInstanceAs (IsQuasiAffine c.pt)
  obtain ⟨j, hj⟩ := Scheme.exists_isQuasiAffine_of_isLimit (ι D) (cone D c) (isLimitCone D hc)
  exact ⟨j.as, hj⟩

include c in
/-- **Stacks Project, Tag 01Z6**: `AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit` with the
index morphism universe unrestricted. -/
public lemma Scheme.exists_isAffine_of_isLimit' (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [IsAffine c.pt] : ∃ i : I, IsAffine (D.obj i) := by
  have : IsAffine (cone D c).pt := inferInstanceAs (IsAffine c.pt)
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit (ι D) (cone D c) (isLimitCone D hc)
  exact ⟨j.as, hj⟩

include c in
/-- **Stacks Project, Tag 01Z4 (2)**: `exists_map_preimage_eq_map_preimage` with the index
morphism universe unrestricted. -/
public lemma exists_map_preimage_eq_map_preimage' (hc : IsLimit c)
    {i : I} {U V : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (hV : IsCompact (V : Set (D.obj i))) (H : c.π.app i ⁻¹ᵁ U = c.π.app i ⁻¹ᵁ V) :
    ∃ (j : I) (f : j ⟶ i), D.map f ⁻¹ᵁ U = D.map f ⁻¹ᵁ V := by
  obtain ⟨j, g, hj⟩ := exists_map_preimage_eq_map_preimage (ι D) (cone D c) (isLimitCone D hc)
    (i := ⟨i⟩) hU hV H
  exact ⟨j.as, hom D g, map_hom D g ▸ hj⟩

include c in
/-- **Stacks Project, Tag 01Z4 (1)**: `exists_isAffineOpen_preimage_eq` with the index morphism
universe unrestricted. -/
public lemma exists_isAffineOpen_preimage_eq' (hc : IsLimit c)
    [∀ i : I, QuasiSeparatedSpace (D.obj i)] (U : c.pt.Opens) (hU : IsAffineOpen U) :
    ∃ (i : I) (V : (D.obj i).Opens), IsAffineOpen V ∧ c.π.app i ⁻¹ᵁ V = U := by
  obtain ⟨j, V, hV, hj⟩ := exists_isAffineOpen_preimage_eq (ι D) (cone D c)
    (isLimitCone D hc) U hU
  exact ⟨j.as, V, hV, hj⟩

include c in
/-- `AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine_of_finite` with the index morphism
universe unrestricted. -/
public lemma Scheme.exists_isOpenCover_and_isAffine_of_finite' (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {J : Type*} [Finite J] (U : J → c.pt.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (hU' : ∀ j, IsAffineOpen (U j)) :
    ∃ (i : I) (V : J → (D.obj i).Opens),
      TopologicalSpace.IsOpenCover V ∧ ∀ j, IsAffineOpen (V j) ∧ U j = c.π.app i ⁻¹ᵁ (V j) := by
  obtain ⟨j, V, hV, hj⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite (ι D) (cone D c)
    (isLimitCone D hc) U hU hU'
  exact ⟨j.as, V, hV, hj⟩

end

section

variable [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

include c in
/-- **Stacks Project, Tag 01ZM (2)**: `AlgebraicGeometry.exists_morphism_after_baseChange` with
the index morphism universe unrestricted, so that no smallness hypothesis on the index category
is needed. -/
public theorem exists_morphism_after_baseChange' (hc : IsLimit c)
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj X ⟶ (Over.pullback (D.map e)).obj Y)
      (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ≅
        (Over.pullback (c.π.app i)).obj X)
      (β : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj Y) ≅
        (Over.pullback (c.π.app i)).obj Y),
      α.hom.left ≫ pullback.fst X.hom (c.π.app i) =
          pullback.fst ((Over.pullback (D.map e)).obj X).hom (c.π.app j) ≫
            pullback.fst X.hom (D.map e) ∧
        β.hom.left ≫ pullback.fst Y.hom (c.π.app i) =
          pullback.fst ((Over.pullback (D.map e)).obj Y).hom (c.π.app j) ≫
            pullback.fst Y.hom (D.map e) ∧
        α.hom ≫ f = (Over.pullback (c.π.app j)).map g ≫ β.hom := by
  obtain ⟨j, e, h⟩ := exists_morphism_after_baseChange (ι D) (cone D c) (isLimitCone D hc)
    ⟨i⟩ X Y hX hY f
  exact ⟨j.as, hom D e, map_hom D e ▸ h⟩

include c in
/-- **Stacks Project, Tag 01ZM (3)**: `AlgebraicGeometry.eventually_eq_of_baseChange_eq` with the
index morphism universe unrestricted, so that no smallness hypothesis on the index category is
needed. -/
public theorem eventually_eq_of_baseChange_eq' (hc : IsLimit c)
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) (f g : X ⟶ Y)
    (hfg : (Over.pullback (c.π.app i)).map f = (Over.pullback (c.π.app i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f = (Over.pullback (D.map e)).map g := by
  obtain ⟨j, e, h⟩ := eventually_eq_of_baseChange_eq (ι D) (cone D c) (isLimitCone D hc)
    ⟨i⟩ X Y hX hY f g hfg
  exact ⟨j.as, hom D e, map_hom D e ▸ h⟩

end

end AlgebraicGeometry

/-! ### Dropping local smallness from the index-universe-free forms

For an index category whose *objects* live anywhere, `ι D` has local `u`-smallness for free, so
the results of `StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit` apply under
`CategoryTheory.InitiallySmall.{u} I` alone. Two instances of the recipe follow; every other
result in that file transfers the same way. -/

namespace AlgebraicGeometry

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

variable {I : Type uI} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  [IsCofiltered I] [InitiallySmall.{u} I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include c in
/-- `AlgebraicGeometry.isAffineHom_π_app_of_initiallySmall` with
`CategoryTheory.LocallySmall.{u} I` dropped. -/
public lemma isAffineHom_π_app_of_initiallySmall' (hc : IsLimit c)
    (i : I) : IsAffineHom (c.π.app i) :=
  isAffineHom_π_app_of_initiallySmall (ι D) (cone D c) (isLimitCone D hc) ⟨i⟩

include c in
/-- **Stacks Project, Tag 01Z4 (1)**:
`AlgebraicGeometry.exists_isAffineOpen_preimage_eq_of_initiallySmall` with
`CategoryTheory.LocallySmall.{u} I` dropped. -/
public lemma exists_isAffineOpen_preimage_eq_of_initiallySmall'
    [∀ i : I, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit c)
    (U : c.pt.Opens) (hU : IsAffineOpen U) :
    ∃ (i : I) (V : (D.obj i).Opens), IsAffineOpen V ∧ c.π.app i ⁻¹ᵁ V = U := by
  obtain ⟨j, V, hV, hj⟩ := exists_isAffineOpen_preimage_eq_of_initiallySmall (ι D) (cone D c)
    (isLimitCone D hc) U hU
  exact ⟨j.as, V, hV, hj⟩

end AlgebraicGeometry

end
