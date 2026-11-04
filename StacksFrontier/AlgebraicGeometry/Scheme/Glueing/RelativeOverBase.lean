module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Relative gluing along an open cover of the base

Let `S` be a scheme and `{Sᵢ}` an open cover of `S`. A family of schemes `pᵢ : Xᵢ ⟶ Sᵢ`
together with transition isomorphisms `pᵢ⁻¹(Sⱼ) ≅ pⱼ⁻¹(Sᵢ)` over `Sᵢ ∩ Sⱼ` satisfying the
cocycle condition on triple overlaps glues to a single scheme `X` over `S` whose restriction
over `Sᵢ` is `Xᵢ`.

The data is packaged as `AlgebraicGeometry.Scheme.RelativeGlueData`. It differs from
`AlgebraicGeometry.Scheme.GlueData` in that the overlaps are not free parameters: they are
forced to be the preimages of the members of the cover of the base, which is exactly what makes
the glued scheme a scheme *over* `S` restricting to the given pieces.

## Main definitions

* `AlgebraicGeometry.Scheme.RelativeGlueData`: the gluing datum relative to an open cover of a
  base scheme.
* `AlgebraicGeometry.Scheme.RelativeGlueData.toGlueData`: the underlying absolute gluing datum.
* `AlgebraicGeometry.Scheme.RelativeGlueData.glued` and
  `AlgebraicGeometry.Scheme.RelativeGlueData.ι`: the glued scheme and its charts.
* `AlgebraicGeometry.Scheme.RelativeGlueData.toBase`: the structure morphism to `S`.
* `AlgebraicGeometry.Scheme.RelativeGlueData.projRestrict`: the structure morphism of a piece,
  viewed as a morphism to the corresponding member of the cover.
* `AlgebraicGeometry.Scheme.RelativeGlueData.ofHom`: a morphism of schemes, viewed as a
  one-chart relative gluing datum over the cover of its target by itself.

## Main results

* `AlgebraicGeometry.Scheme.RelativeGlueData.ι_toBase`: the structure morphism restricts on the
  `i`-th chart to the given `pᵢ`.
* `AlgebraicGeometry.Scheme.RelativeGlueData.toBase_preimage_eq_opensRange_ι`: the `i`-th chart
  is exactly the preimage of `Sᵢ` under the structure morphism.
* `AlgebraicGeometry.Scheme.RelativeGlueData.isPullback_projRestrict_ι`: consequently `Xᵢ` is
  the fibre product `X ×_S Sᵢ`, i.e. the chart identifies `Xᵢ` with the part of `X` over `Sᵢ`,
  compatibly with the structure morphisms.
* `AlgebraicGeometry.Scheme.RelativeGlueData.hom_ext`: two morphisms out of the glued scheme
  agreeing on every chart are equal, so the glued scheme over `S` is unique up to unique
  isomorphism.
* `AlgebraicGeometry.Scheme.RelativeGlueData.eq_t'_of_fac`: the transition morphism on triple
  overlaps is determined by the one on double overlaps.
* `AlgebraicGeometry.Scheme.RelativeGlueData.ι_toBase_ofHom`: the relative gluing of a morphism
  over the trivial cover of its target is that morphism again.

## Implementation notes

The overlap `pᵢ⁻¹(Sⱼ)` is an open subscheme of `Xᵢ`, so the intersection of two overlaps inside
`Xᵢ` is their infimum as opens rather than a pullback. The transition map on triple overlaps is
therefore asked for in the infimum presentation, and `AlgebraicGeometry.isPullback_opens_inf`
transports it to the pullback presentation that `AlgebraicGeometry.Scheme.GlueData` expects.
Fields are stated with the overlaps written out, so that the structure can be built without any
side conditions; `AlgebraicGeometry.Scheme.RelativeGlueData.overlap` is a reducible abbreviation
used afterwards. As with `AlgebraicGeometry.Scheme.GlueData`, the triple-overlap transition is
asked for as data, but it is uniquely determined by its compatibility with the double-overlap
transition.

That `pᵢ` factors through `Sᵢ` is recorded as the statement that the preimage of `Sᵢ` is all of
`Xᵢ`, which is also what makes the inclusion of the self-overlap an isomorphism.

No affineness is needed anywhere: the cover of the base is an arbitrary open cover.

The companion presentation of relative gluing, in which the local data is indexed by a basis of
the topology of `S` ordered by inclusion and the compatibility is expressed by restriction
morphisms rather than by a cocycle, is
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A gluing datum relative to an open cover of a base scheme `S`: an open cover `{base i}` of
`S`, a scheme `obj i` over each `base i`, and transition isomorphisms between the preimages of
`base j` in `obj i` and of `base i` in `obj j`, subject to the cocycle condition.

Unlike `AlgebraicGeometry.Scheme.GlueData`, the overlaps are not part of the data: they are the
preimages of the members of the cover of the base. -/
structure RelativeGlueData (S : Scheme.{u}) where
  /-- The index type of the cover of the base. -/
  J : Type u
  /-- The `i`-th member of the open cover of the base. -/
  base : J → S.Opens
  /-- The members of `base` cover the base. -/
  iSup_base : ⨆ i, base i = ⊤
  /-- The scheme living over the `i`-th member of the cover. -/
  obj : J → Scheme.{u}
  /-- The structure morphism of `obj i`, as a morphism to the base. -/
  proj : ∀ i, obj i ⟶ S
  /-- The structure morphism of `obj i` factors through `base i`. -/
  proj_preimage_eq_top : ∀ i, proj i ⁻¹ᵁ base i = ⊤
  /-- The transition isomorphism over `base i ⊓ base j`. -/
  t : ∀ i j, (proj i ⁻¹ᵁ base j).toScheme ⟶ (proj j ⁻¹ᵁ base i).toScheme
  /-- The transitions are morphisms over the base. -/
  t_over : ∀ i j, t i j ≫ (proj j ⁻¹ᵁ base i).ι ≫ proj j = (proj i ⁻¹ᵁ base j).ι ≫ proj i
  /-- The transition from a piece to itself is the identity. -/
  t_self : ∀ i, t i i = 𝟙 _
  /-- The transition isomorphism on triple overlaps. -/
  t' : ∀ i j k, (proj i ⁻¹ᵁ base j ⊓ proj i ⁻¹ᵁ base k).toScheme ⟶
    (proj j ⁻¹ᵁ base k ⊓ proj j ⁻¹ᵁ base i).toScheme
  /-- On triple overlaps the transition isomorphism restricts the one on double overlaps. -/
  t'_fac : ∀ i j k, t' i j k ≫ (obj j).homOfLE inf_le_right =
    (obj i).homOfLE inf_le_left ≫ t i j
  /-- The cocycle condition. -/
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

namespace RelativeGlueData

variable {S : Scheme.{u}} (D : RelativeGlueData S)

/-- The overlap `pᵢ⁻¹(Sⱼ)`, an open subscheme of `obj i`. -/
abbrev overlap (i j : D.J) : (D.obj i).Opens := D.proj i ⁻¹ᵁ D.base j

/-- Every point of a piece lies over the corresponding member of the cover of the base. -/
lemma proj_mem_base (i : D.J) (y : D.obj i) : D.proj i y ∈ D.base i :=
  show y ∈ D.proj i ⁻¹ᵁ D.base i from (D.proj_preimage_eq_top i).ge trivial

/-- The self-overlap of a piece is everything, since `pᵢ` factors through `Sᵢ`. -/
lemma overlap_self (i : D.J) : D.overlap i i = ⊤ := D.proj_preimage_eq_top i

/-- The inclusion of the self-overlap `pᵢ⁻¹(Sᵢ)` into `obj i` is an isomorphism. -/
instance isIso_overlap_self_ι (i : D.J) : IsIso (D.overlap i i).ι :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ <| by
    rw [Opens.opensRange_ι, D.overlap_self]

/-- The intersection of two overlaps inside `obj i`, as the pullback of their inclusions. -/
def overlapPullbackIso (i j k : D.J) :
    (D.overlap i j ⊓ D.overlap i k).toScheme ≅ pullback (D.overlap i j).ι (D.overlap i k).ι :=
  (isPullback_opens_inf (D.overlap i j) (D.overlap i k)).isoPullback

/-- The first projection of the intersection of two overlaps, read through
`AlgebraicGeometry.Scheme.RelativeGlueData.overlapPullbackIso`. -/
@[reassoc (attr := simp)]
lemma overlapPullbackIso_inv_fst (i j k : D.J) :
    (D.overlapPullbackIso i j k).inv ≫ (D.obj i).homOfLE inf_le_left =
      pullback.fst (D.overlap i j).ι (D.overlap i k).ι :=
  (isPullback_opens_inf (D.overlap i j) (D.overlap i k)).isoPullback_inv_fst

/-- The second projection of the intersection of two overlaps, read through
`AlgebraicGeometry.Scheme.RelativeGlueData.overlapPullbackIso`. -/
@[reassoc (attr := simp)]
lemma overlapPullbackIso_hom_snd (i j k : D.J) :
    (D.overlapPullbackIso i j k).hom ≫ pullback.snd (D.overlap i j).ι (D.overlap i k).ι =
      (D.obj i).homOfLE inf_le_right :=
  (isPullback_opens_inf (D.overlap i j) (D.overlap i k)).isoPullback_hom_snd

/-- The transition morphism on triple overlaps is determined by the one on double overlaps, so
`AlgebraicGeometry.Scheme.RelativeGlueData.t'` carries no information beyond the assertion that
`t i j` restricts to the triple overlap. -/
lemma eq_t'_of_fac (i j k : D.J)
    (u : (D.overlap i j ⊓ D.overlap i k).toScheme ⟶ (D.overlap j k ⊓ D.overlap j i).toScheme)
    (hu : u ≫ (D.obj j).homOfLE inf_le_right = (D.obj i).homOfLE inf_le_left ≫ D.t i j) :
    u = D.t' i j k := by
  have : Mono ((D.obj j).homOfLE (inf_le_right : D.overlap j k ⊓ D.overlap j i ≤ _)) :=
    mono_of_mono_fac ((D.obj j).homOfLE_ι _)
  rw [← cancel_mono ((D.obj j).homOfLE (inf_le_right : D.overlap j k ⊓ D.overlap j i ≤ _)), hu,
    D.t'_fac]

/-- The absolute gluing datum underlying a relative one: the overlaps are the preimages of the
members of the cover of the base, and the transition maps on triple overlaps are transported
from the infimum presentation to the pullback presentation. -/
@[implicit_reducible] def toGlueData : Scheme.GlueData.{u} where
  J := D.J
  U := D.obj
  V ij := (D.overlap ij.1 ij.2).toScheme
  f i j := (D.overlap i j).ι
  f_id i := D.isIso_overlap_self_ι i
  t := D.t
  t_id := D.t_self
  t' i j k :=
    (D.overlapPullbackIso i j k).inv ≫ D.t' i j k ≫ (D.overlapPullbackIso j k i).hom
  t_fac i j k := by
    rw [Category.assoc, Category.assoc, D.overlapPullbackIso_hom_snd, D.t'_fac,
      ← Category.assoc, D.overlapPullbackIso_inv_fst]
  cocycle i j k := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (D.t' j k i), ← Category.assoc (D.t' i j k), D.cocycle i j k,
      Category.id_comp, Iso.inv_hom_id]
  f_open i j := inferInstance

/-- The scheme obtained by gluing the pieces of a relative gluing datum. -/
abbrev glued : Scheme.{u} := D.toGlueData.glued

/-- The `i`-th chart of the glued scheme. -/
abbrev ι (i : D.J) : D.obj i ⟶ D.glued := D.toGlueData.ι i

/-- Each chart of the glued scheme is an open immersion. -/
instance isOpenImmersion_ι (i : D.J) : IsOpenImmersion (D.ι i) :=
  D.toGlueData.ι_isOpenImmersion i

/-- The charts of the glued scheme cover it. -/
lemma ι_jointly_surjective (x : D.glued) : ∃ (i : D.J) (y : D.obj i), D.ι i y = x :=
  D.toGlueData.ι_jointly_surjective x

/-- The two transition morphisms attached to a pair of indices are mutually inverse. -/
@[reassoc (attr := simp)]
lemma t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙 _ := D.toGlueData.t_inv i j

/-- Each transition morphism `t i j` is an isomorphism. -/
instance isIso_t (i j : D.J) : IsIso (D.t i j) := D.toGlueData.t_isIso i j

/-- The charts are compatible with the transition morphisms: passing from the `i`-th to the
`j`-th chart through the transition morphism does not change the point of the glued scheme. -/
@[reassoc]
lemma t_ι (i j : D.J) : D.t i j ≫ (D.overlap j i).ι ≫ D.ι j = (D.overlap i j).ι ≫ D.ι i :=
  D.toGlueData.glue_condition i j

/-- The structure morphism of the glued scheme, obtained by gluing the structure morphisms of
the pieces. -/
def toBase : D.glued ⟶ S :=
  Multicoequalizer.desc D.toGlueData.diagram S D.proj <| by
    rintro ⟨i, j⟩
    change (D.overlap i j).ι ≫ D.proj i = D.t i j ≫ (D.overlap j i).ι ≫ D.proj j
    exact (D.t_over i j).symm

/-- The structure morphism of the glued scheme restricts on the `i`-th chart to the structure
morphism of the `i`-th piece. -/
@[reassoc (attr := simp)]
lemma ι_toBase (i : D.J) : D.ι i ≫ D.toBase = D.proj i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- The structure morphism of the glued scheme sends a point of the `i`-th chart to its image
under the structure morphism of the `i`-th piece. -/
lemma toBase_ι_apply (i : D.J) (y : D.obj i) : D.toBase (D.ι i y) = D.proj i y := by
  rw [← Scheme.Hom.comp_apply, D.ι_toBase]

/-- The `i`-th chart of the glued scheme is exactly the part lying over the `i`-th member of
the cover of the base. -/
lemma toBase_preimage_eq_range_ι (i : D.J) :
    D.toBase ⁻¹' (D.base i : Set S) = Set.range (D.ι i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, y, rfl⟩ := D.toGlueData.ι_jointly_surjective x
    have hy : y ∈ D.overlap j i := show D.proj j y ∈ D.base i from D.toBase_ι_apply j y ▸ hx
    exact ⟨_, congr($(D.toGlueData.glue_condition j i) (⟨y, hy⟩ : D.overlap j i))⟩
  · rintro ⟨y, rfl⟩
    exact show D.toBase (D.ι i y) ∈ D.base i from
      (D.toBase_ι_apply i y).symm ▸ D.proj_mem_base i y

/-- The `i`-th chart of the glued scheme is exactly the preimage of the `i`-th member of the
cover of the base, as open subschemes. -/
lemma toBase_preimage_eq_opensRange_ι (i : D.J) :
    D.toBase ⁻¹ᵁ D.base i = (D.ι i).opensRange :=
  TopologicalSpace.Opens.coe_inj.mp (D.toBase_preimage_eq_range_ι i)

/-- The structure morphism of the `i`-th piece, as a morphism to the `i`-th member of the cover
of the base. -/
def projRestrict (i : D.J) : D.obj i ⟶ (D.base i).toScheme :=
  IsOpenImmersion.lift (D.base i).ι (D.proj i) <| by
    rw [Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact D.proj_mem_base i y

/-- The structure morphism of the `i`-th piece factors through the `i`-th member of the cover
of the base. -/
@[reassoc (attr := simp)]
lemma projRestrict_ι (i : D.J) : D.projRestrict i ≫ (D.base i).ι = D.proj i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The `i`-th chart identifies the `i`-th piece with the part of the glued scheme lying over
the `i`-th member of the cover of the base. -/
lemma isPullback_projRestrict_ι (i : D.J) :
    IsPullback (D.projRestrict i) (D.ι i) (D.base i).ι D.toBase :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp) <| by
    rw [Opens.opensRange_ι, D.toBase_preimage_eq_opensRange_ι]

/-- Two morphisms out of the glued scheme which agree on every chart are equal. -/
lemma hom_ext {Y : Scheme.{u}} {a b : D.glued ⟶ Y} (h : ∀ i, D.ι i ≫ a = D.ι i ≫ b) : a = b :=
  Multicoequalizer.hom_ext _ _ _ h

section OfHom

variable {X : Scheme.{u}} (f : X ⟶ S)

/-- A morphism `f : X ⟶ S` is itself a relative gluing datum, over the cover of `S` by `S`:
there is one chart, namely `X`, and the transition morphism is the identity. -/
@[implicit_reducible] def ofHom : RelativeGlueData S where
  J := PUnit.{u + 1}
  base _ := ⊤
  iSup_base := by simp
  obj _ := X
  proj _ := f
  proj_preimage_eq_top _ := rfl
  t _ _ := 𝟙 _
  t_over _ _ := Category.id_comp _
  t_self _ := rfl
  t' _ _ _ := 𝟙 _
  t'_fac _ _ _ := by simp
  cocycle _ _ _ := by simp

/-- The unique chart of the relative gluing of a morphism `f` is an isomorphism. -/
instance isIso_ofHom_ι : IsIso ((ofHom f).ι ⟨⟩) :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ <| by
    ext x
    obtain ⟨⟨⟩, y, hy⟩ := (ofHom f).ι_jointly_surjective x
    simpa using ⟨y, hy⟩

/-- The relative gluing of a morphism over the trivial cover of its target returns that
morphism: the unique chart is an isomorphism onto the glued scheme and carries the structure
morphism of the gluing back to `f`. -/
lemma ι_toBase_ofHom : (ofHom f).ι ⟨⟩ ≫ (ofHom f).toBase = f :=
  (ofHom f).ι_toBase ⟨⟩

end OfHom

end RelativeGlueData

end AlgebraicGeometry.Scheme

end
