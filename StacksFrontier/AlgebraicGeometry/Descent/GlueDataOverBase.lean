module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing schemes over a base along open subschemes

Let `S` be a scheme. A family of schemes `pᵢ : Xᵢ ⟶ S` over `S`, together with open subschemes
`Xᵢⱼ ⊆ Xᵢ` with `Xᵢᵢ = Xᵢ` and isomorphisms `Xᵢⱼ ≅ Xⱼᵢ` over `S` satisfying the cocycle condition
on triple overlaps, glues to a single scheme `X` over `S` in which each `Xᵢ` is an open subscheme
and `Xᵢⱼ` is the intersection `Xᵢ ∩ Xⱼ`.

The pieces and the transition isomorphisms are required to live over `S`, and the glued scheme
therefore carries a structure morphism to `S` restricting to the given `pᵢ`.

## Main definitions

* `AlgebraicGeometry.Scheme.GlueDataOverBase`: the gluing datum.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.toGlueData`: the underlying absolute gluing datum.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.glued` and
  `AlgebraicGeometry.Scheme.GlueDataOverBase.ι`: the glued scheme and its charts.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.toBase`: the structure morphism to `S`.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.overlapPullbackIso`: the intersection of two
  overlaps inside a piece, read as a fibre product.

## Main results

* `AlgebraicGeometry.Scheme.GlueDataOverBase.ι_toBase`: the structure morphism of the glued
  scheme restricts on the `i`-th chart to the given `pᵢ`.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.preimage_opensRange_ι`: the prescribed overlap
  `Xᵢⱼ` is exactly the part of the `i`-th chart lying in the `j`-th chart, so the glued scheme
  realizes `Xᵢⱼ` as `Xᵢ ∩ Xⱼ`.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.iSup_opensRange_ι`: the charts cover the glued
  scheme.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.eq_t'_of_fac`: the transition morphism on triple
  overlaps is determined by the one on double overlaps.

## Implementation notes

The overlaps `Xᵢⱼ` are open subschemes of `Xᵢ`, so the intersection of two of them inside `Xᵢ`
is their infimum as opens rather than a pullback. The transition map on triple overlaps is
therefore asked for in the infimum presentation, and `AlgebraicGeometry.isPullback_opens_inf`
transports it to the pullback presentation that `AlgebraicGeometry.Scheme.GlueData` expects.
That the self-overlap is everything is what makes the inclusion of the self-overlap an
isomorphism, which `AlgebraicGeometry.Scheme.GlueData` requires.

In `AlgebraicGeometry.Scheme.RelativeGlueData` the overlaps are not free parameters but the
preimages of the members of a fixed open cover of the base; here the pieces are arbitrary schemes
over `S` glued along arbitrary opens.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 01JB](https://stacks.math.columbia.edu/tag/01JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A gluing datum of schemes over a base scheme `S`: a family of schemes `obj i` over `S`, an
open subscheme `overlap i j` of `obj i` for each pair of indices, with `overlap i i` everything,
and transition isomorphisms `overlap i j ≅ overlap j i` over `S` subject to the cocycle
condition.

Unlike `AlgebraicGeometry.Scheme.RelativeGlueData`, the overlaps are arbitrary opens of the
pieces rather than preimages of the members of a cover of the base. -/
structure GlueDataOverBase (S : Scheme.{u}) where
  /-- The index type of the family of pieces. -/
  J : Type u
  /-- The `i`-th piece. -/
  obj : J → Scheme.{u}
  /-- The structure morphism of the `i`-th piece. -/
  proj : ∀ i, obj i ⟶ S
  /-- The part of the `i`-th piece that is glued to the `j`-th piece. -/
  overlap : ∀ i, J → (obj i).Opens
  /-- A piece is glued to itself along the whole of itself. -/
  overlap_self : ∀ i, overlap i i = ⊤
  /-- The transition isomorphism from the `(i, j)`-th overlap to the `(j, i)`-th one. -/
  t : ∀ i j, (overlap i j).toScheme ⟶ (overlap j i).toScheme
  /-- The transitions are morphisms over the base. -/
  t_over : ∀ i j, t i j ≫ (overlap j i).ι ≫ proj j = (overlap i j).ι ≫ proj i
  /-- The transition from a piece to itself is the identity. -/
  t_self : ∀ i, t i i = 𝟙 _
  /-- The transition isomorphism on triple overlaps. -/
  t' : ∀ i j k, (overlap i j ⊓ overlap i k).toScheme ⟶ (overlap j k ⊓ overlap j i).toScheme
  /-- On triple overlaps the transition isomorphism restricts the one on double overlaps. -/
  t'_fac : ∀ i j k, t' i j k ≫ (obj j).homOfLE inf_le_right =
    (obj i).homOfLE inf_le_left ≫ t i j
  /-- The cocycle condition. -/
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

namespace GlueDataOverBase

variable {S : Scheme.{u}} (D : GlueDataOverBase S)

/-- The inclusion of the self-overlap of a piece is an isomorphism. -/
instance isIso_overlap_self_ι (i : D.J) : IsIso (D.overlap i i).ι :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ <| by
    rw [Opens.opensRange_ι, D.overlap_self]

/-- The intersection of two overlaps inside a piece, as the pullback of their inclusions. -/
def overlapPullbackIso (i j k : D.J) :
    (D.overlap i j ⊓ D.overlap i k).toScheme ≅ pullback (D.overlap i j).ι (D.overlap i k).ι :=
  (isPullback_opens_inf (D.overlap i j) (D.overlap i k)).isoPullback

/-- The first projection of the intersection of two overlaps, read through
`AlgebraicGeometry.Scheme.GlueDataOverBase.overlapPullbackIso`. -/
@[reassoc (attr := simp)]
lemma overlapPullbackIso_inv_fst (i j k : D.J) :
    (D.overlapPullbackIso i j k).inv ≫ (D.obj i).homOfLE inf_le_left =
      pullback.fst (D.overlap i j).ι (D.overlap i k).ι :=
  (isPullback_opens_inf (D.overlap i j) (D.overlap i k)).isoPullback_inv_fst

/-- The second projection of the intersection of two overlaps, read through
`AlgebraicGeometry.Scheme.GlueDataOverBase.overlapPullbackIso`. -/
@[reassoc (attr := simp)]
lemma overlapPullbackIso_hom_snd (i j k : D.J) :
    (D.overlapPullbackIso i j k).hom ≫ pullback.snd (D.overlap i j).ι (D.overlap i k).ι =
      (D.obj i).homOfLE inf_le_right :=
  (isPullback_opens_inf (D.overlap i j) (D.overlap i k)).isoPullback_hom_snd

/-- The transition morphism on triple overlaps is determined by the one on double overlaps, so
`AlgebraicGeometry.Scheme.GlueDataOverBase.t'` carries no information beyond the assertion that
`t i j` restricts to the triple overlap. -/
lemma eq_t'_of_fac (i j k : D.J)
    (u : (D.overlap i j ⊓ D.overlap i k).toScheme ⟶ (D.overlap j k ⊓ D.overlap j i).toScheme)
    (hu : u ≫ (D.obj j).homOfLE inf_le_right = (D.obj i).homOfLE inf_le_left ≫ D.t i j) :
    u = D.t' i j k := by
  have : Mono ((D.obj j).homOfLE (inf_le_right : D.overlap j k ⊓ D.overlap j i ≤ _)) :=
    mono_of_mono_fac ((D.obj j).homOfLE_ι _)
  rw [← cancel_mono ((D.obj j).homOfLE (inf_le_right : D.overlap j k ⊓ D.overlap j i ≤ _)), hu,
    D.t'_fac]

/-- The absolute gluing datum underlying a gluing datum over a base: the overlaps are the
prescribed opens, and the transition maps on triple overlaps are transported from the infimum
presentation to the pullback presentation. -/
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

/-- The scheme obtained by gluing the pieces of a gluing datum over a base. -/
abbrev glued : Scheme.{u} := D.toGlueData.glued

/-- The `i`-th chart of the glued scheme. -/
abbrev ι (i : D.J) : D.obj i ⟶ D.glued := D.toGlueData.ι i

/-- Each chart of the glued scheme is an open immersion. -/
instance isOpenImmersion_ι (i : D.J) : IsOpenImmersion (D.ι i) :=
  D.toGlueData.ι_isOpenImmersion i

/-- The charts of the glued scheme cover it. -/
lemma ι_jointly_surjective (x : D.glued) : ∃ (i : D.J) (y : D.obj i), D.ι i y = x :=
  D.toGlueData.ι_jointly_surjective x

/-- The images of the charts cover the glued scheme. -/
lemma iSup_opensRange_ι : ⨆ i, (D.ι i).opensRange = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩

/-- The two transition morphisms attached to a pair of indices are mutually inverse. -/
@[reassoc (attr := simp)]
lemma t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙 _ := D.toGlueData.t_inv i j

/-- The transition morphisms are isomorphisms. -/
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

/-- The `i`-th chart identifies the `(i, j)`-th overlap with the part of the `i`-th piece lying
in the `j`-th chart. -/
lemma isPullback_ι (i j : D.J) :
    IsPullback (D.overlap i j).ι (D.t i j ≫ (D.overlap j i).ι) (D.ι i) (D.ι j) :=
  IsPullback.of_isLimit (D.toGlueData.vPullbackConeIsLimit i j)

/-- **The prescribed overlap is the intersection of the two charts.** The part of the `i`-th
piece which lands in the `j`-th chart of the glued scheme is exactly `overlap i j`. -/
lemma preimage_opensRange_ι (i j : D.J) : D.ι i ⁻¹ᵁ (D.ι j).opensRange = D.overlap i j := by
  have hcomp : ((D.isPullback_ι i j).isoPullback.hom ≫
      pullback.fst (D.ι i) (D.ι j)).opensRange = D.ι i ⁻¹ᵁ (D.ι j).opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]
  rw [← hcomp]
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange, (D.isPullback_ι i j).isoPullback_hom_fst,
    Scheme.Opens.range_ι]

end GlueDataOverBase

end AlgebraicGeometry.Scheme

end
