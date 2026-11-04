module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreProperty
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulayDimOne
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# Semistable families of curves of a given genus

The stack of semistable curves decomposes as the disjoint union, over `g ≥ 1`, of open and closed
substacks `Curves^{semistable}_g` (Stacks 0E71): a family of curves `f : X → S` lies in the
genus-`g` piece when it is semistable and `R¹f_*𝒪_X` is locally free of rank `g`, and a proper
curve over a field lies in it when it is semistable of genus `g`.

This file develops the decomposition at the level of families of curves, with the genus read on
the fibres. The fibre of a family of curves at a field-valued point `p` of its base *has genus
`g`* when it is presented by a scheme over the field of `p` of genus `g`. The genus of a fibre does
not depend on the presentation and is unchanged by extension of the field of the point, because
the presentation over an extension is a base change of the presentation over the point and the
genus of a proper scheme over a field is invariant under extension of the ground field (Stacks
0BY9). Consequently, for a family whose fibres are presented by schemes — every semistable family —
the genus at a field-valued point depends only on the underlying point of the base scheme, and the
base is the disjoint union of the *genus loci*: the sets of points at which the fibre has genus
`g`. For a semistable family only positive genera occur. A morphism of families of curves `X → Y`
identifies the fibres of `X` with those of `Y` at the image points, so the genus loci of `X` are
the inverse images of those of `Y`: the formation of the genus loci commutes with arbitrary base
change.

A family is semistable of genus `g` when it is semistable and its genus-`g` locus is the whole
base. These families form the strictly full subcategory `Curves^{semistable}_g` of the category of
families of curves; it is contained in `Curves^{semistable}`, its objects over a nonempty base have
a single genus, which is positive, and a semistable family over a base with one point lies in
exactly one piece. A family mapping to a semistable family `Y` lies in the genus-`g` piece exactly
when its morphism of bases lands in the genus-`g` locus of `Y`. Finally, for a proper scheme `T` of
dimension at most one over a field `k`, the family of curves `T → Spec(k)` is semistable of genus
`n` exactly when it is semistable and `T` has genus `n` over `k`, which is the genus clause of part
(2) of Stacks 0E71.

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasGenusAt`: the fibre at a field-valued point of the base has
  genus `g`, the instance of `AlgebraicGeometry.CurveFamily.HasFibreSatisfying` for the genus.
* `AlgebraicGeometry.CurveFamily.HasFibresOfGenus`: all fibres have genus `g`.
* `AlgebraicGeometry.CurveFamily.genusLocus`: the set of points of the base at which the fibre has
  genus `g`.
* `AlgebraicGeometry.IsSemistableCurveFamilyOfFibreGenus`: semistable with all fibres of genus `g`.
* `AlgebraicGeometry.CurvesSemistableOfFibreGenus`: the strictly full subcategory
  `Curves^{semistable}_g`.

## Main results

* `AlgebraicGeometry.CurveFamily.genus_eq_of_dominates`: the genus of a fibre is unchanged by
  extension of the field of the point; `AlgebraicGeometry.CurveFamily.HasGenusAt.unique`: the
  genus of a fibre is unique.
* `AlgebraicGeometry.CurveFamily.hasFibreSatisfying_map_iff`: a fibre condition holds at a point
  exactly when it holds for a target family at the image point.
* `AlgebraicGeometry.CurveFamily.hasGenusAt_map_iff` and
  `AlgebraicGeometry.CurveFamily.genusLocus_eq_preimage`: the genus of the fibres and the genus
  loci commute with base change.
* `AlgebraicGeometry.IsSemistableCurveFamily.existsUnique_mem_genusLocus`,
  `AlgebraicGeometry.IsSemistableCurveFamily.iUnion_genusLocus` and
  `AlgebraicGeometry.CurveFamily.disjoint_genusLocus`: the base of a semistable family is the
  disjoint union of its genus loci of positive genus.
* `AlgebraicGeometry.curvesSemistableOfFibreGenus_isClosedUnderIsomorphisms` and
  `AlgebraicGeometry.CurveFamily.isSemistableCurveFamilyOfFibreGenus_of_hom`: the genus-`g`
  piece is strictly full and stable under base change.
* `AlgebraicGeometry.IsSemistableCurveFamilyOfFibreGenus.unique`,
  `AlgebraicGeometry.IsSemistableCurveFamilyOfFibreGenus.one_le` and
  `AlgebraicGeometry.IsSemistableCurveFamily.existsUnique_isSemistableCurveFamilyOfFibreGenus`:
  the pieces are disjoint, of positive genus, and cover the families over a one-point base.
* `AlgebraicGeometry.isSemistableCurveFamilyOfFibreGenus_iff_range_subset`: a family mapping to a
  semistable family lies in the genus-`g` piece exactly when its base maps into the genus-`g`
  locus.
* `AlgebraicGeometry.isSemistableCurveFamilyOfFibreGenus_curveFamilyOfSchemeMorphism_iff`: over a
  field, semistability of genus `n` is semistability together with genus `n`.

## Implementation notes

The genus condition of the source on a family is that `R¹f_*𝒪_X` is a locally free
`𝒪_S`-module of rank `g`. For a prestable family, in particular a semistable one, `R¹f_*𝒪_X` is
finite locally free and its formation commutes with arbitrary base change (Stacks 0E1J), so its
rank at a point `s` of the base is `dim H¹(X_s, 𝒪_{X_s})`, the genus of the fibre; the condition is
therefore that every fibre has genus `g`, which is the form used here. That `Curves^{semistable}_g`
is an open and closed substack is the local constancy of the genus on the prestable locus
(Stacks 0E6V) combined with the openness of the semistable locus (Stacks 0E70); neither is proved
here, so the genus loci are not shown to be open.

A point of the base is a field-valued point in the sense of Stacks 03BU, and the fibre there is
presented by a scheme exactly as in `AlgebraicGeometry.IsSemistableCurveFamily`. Semistability
supplies such a presentation at every field-valued point; this is what makes the genus at a
field-valued point depend only on the underlying point of the base.

## References

* [Stacks Project, Tag 0E71](https://stacks.math.columbia.edu/tag/0E71)
* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E6Z](https://stacks.math.columbia.edu/tag/0E6Z)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- A scheme presenting the fibre of a family of curves at a field-valued point of its base is
proper over the field of the point. -/
theorem isProper_toScheme_map_of_isPullback (X : CurveFamily B hZ)
    {W V : BigFppfOver B integerBase hZ} (z : yoneda.obj W ⟶ (schemeSpace X.base).obj)
    (v : V ⟶ W) (q : yoneda.obj V ⟶ X.total.obj)
    (h : IsPullback q (yoneda.map v) X.toBase.hom z) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) := by
  have h₁ : Space.IsProper B integerBase hZ (yoneda.map v) :=
    (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback
      (Space.isPullback_homMk B integerBase hZ X.total.2
        (isAlgebraicSpace_yoneda B integerBase hZ W) (schemeSpace X.base).2
        (isAlgebraicSpace_yoneda B integerBase hZ V) h) X.proper
  have h₂ := (Space.presheaf_isProper_iff B integerBase hZ (yoneda.map v)
    (isAlgebraicSpace_yoneda B integerBase hZ V) (isAlgebraicSpace_yoneda B integerBase hZ W)
    (Functor.relativelyRepresentable.map _ _)).1 h₁
  exact h₂.property (𝟙 _) (𝟙 _) v (IsPullback.of_horiz_isIso ⟨by simp⟩)

/-- A cartesian square of representables in the big fppf site gives a cartesian square of
schemes. -/
private theorem isPullback_toScheme_map_preimage {T V W U : BigFppfOver B integerBase hZ}
    {q : yoneda.obj T ⟶ yoneda.obj V} {a : T ⟶ W} {b : V ⟶ U} {c : W ⟶ U}
    (h : IsPullback q (yoneda.map a) (yoneda.map b) (yoneda.map c)) :
    IsPullback ((BigFppfOver.toScheme B integerBase hZ).map (Yoneda.fullyFaithful.preimage q))
      ((BigFppfOver.toScheme B integerBase hZ).map a)
      ((BigFppfOver.toScheme B integerBase hZ).map b)
      ((BigFppfOver.toScheme B integerBase hZ).map c) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B integerBase hZ) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  exact (IsPullback.of_map_of_faithful yoneda (by rwa [Yoneda.fullyFaithful.map_preimage])).map _

/-- **The genus of a fibre is unchanged by extension of the field of the point.** Let `r` be a
field-valued point of the base of a family of curves which is the restriction of a field-valued
point `p` along a morphism `f` of field spectra. Then a scheme presenting the fibre at `r` has the
same genus, over the field of `r`, as a scheme presenting the fibre at `p`, over the field of `p`.

The presentation at `r` is the base change of the presentation at `p` along `f`, by pasting
cartesian squares of algebraic spaces; all four corners of the resulting square are schemes, so it
is a cartesian square of schemes, and the genus of a proper scheme over a field is unchanged by
extension of the ground field (Stacks 0BY9). -/
theorem genus_eq_of_dominates (X : CurveFamily B hZ)
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    (f : r.siteObject ⟶ p.siteObject) (hf : (schemeSpace X.base).obj.map f.op p.value = r.value)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ r.siteObject) (q' : yoneda.obj W ⟶ X.total.obj)
    (hW : IsPullback q' (yoneda.map w) X.toBase.hom (yonedaEquiv.symm r.value)) :
    genus ((BigFppfOver.toScheme B integerBase hZ).map w) =
      genus ((BigFppfOver.toScheme B integerBase hZ).map v) := by
  set F := BigFppfOver.toScheme B integerBase hZ
  have hr : yonedaEquiv.symm r.value = yoneda.map f ≫ yonedaEquiv.symm p.value := by
    rw [← hf, yonedaEquiv_symm_map]
    rfl
  let l : yoneda.obj W ⟶ yoneda.obj V :=
    hV.lift q' (yoneda.map (w ≫ f)) (by rw [hW.w, hr, Functor.map_comp, Category.assoc])
  have hl₁ : l ≫ q = q' := hV.lift_fst _ _ _
  have hl₂ : l ≫ yoneda.map v = yoneda.map (w ≫ f) := hV.lift_snd _ _ _
  have hsq : IsPullback l (yoneda.map w) (yoneda.map v) (yoneda.map f) :=
    IsPullback.of_right (h₁₂ := q) (h₂₂ := yonedaEquiv.symm p.value)
      (v₁₃ := X.toBase.hom) (by rwa [hl₁, ← hr]) (by rw [hl₂, Functor.map_comp]) hV
  have hsqS := isPullback_toScheme_map_preimage hsq
  have hFf : F.map f = Spec.map (CommRingCat.ofHom (Spec.preimage (F.map f)).hom) := by
    simp
  have := X.isProper_toScheme_map_of_isPullback _ v q hV
  rw [hFf] at hsqS
  exact genus_eq_of_isPullback p.carrier r.carrier (Spec.preimage (F.map f)).hom
    _ (F.map w) (F.map v) hsqS

/-- **The genus of a fibre does not depend on its presentation.** Two schemes presenting the
fibre of a family of curves at the same field-valued point of its base have the same genus. -/
theorem genus_eq_of_isPullback_of_isPullback (X : CurveFamily B hZ)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ p.siteObject) (q' : yoneda.obj W ⟶ X.total.obj)
    (hW : IsPullback q' (yoneda.map w) X.toBase.hom (yonedaEquiv.symm p.value)) :
    genus ((BigFppfOver.toScheme B integerBase hZ).map w) =
      genus ((BigFppfOver.toScheme B integerBase hZ).map v) :=
  X.genus_eq_of_dominates (𝟙 _) (by simp) v q hV w q' hW

/-- A scheme presenting the fibre of a family of curves at a field-valued point of its base
presents the fibre of every family it maps to at the image point: paste the cartesian square of
the morphism of families. -/
theorem isPullback_comp_totalMap {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ X.total.obj}
    (h : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value)) :
    IsPullback (q ≫ φ.totalMap.hom) (yoneda.map v) Y.toBase.hom
      (yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
        (schemeSpaceMap φ.baseMap).hom p).value) := by
  have hval : yonedaEquiv.symm
      (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p).value =
        yonedaEquiv.symm p.value ≫ (schemeSpaceMap φ.baseMap).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  exact (congrArg (IsPullback (q ≫ φ.totalMap.hom) (yoneda.map v) Y.toBase.hom) hval).mpr
    (h.paste_horiz (AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian))

/-- **Fibre conditions pass to the target of a morphism of families of curves.** For a morphism
`φ : X ⟶ Y` of families and a field-valued point `p` of the base of `X`, if the fibre of `X` at `p`
satisfies `P` then so does the fibre of `Y` at the image of `p`: the fibre of `X` at `p` is the
fibre of `Y` at the image point. -/
theorem hasFibreSatisfying_map
    {P : ∀ (k : Type u) [Field k] {V : Scheme.{u}}, (V ⟶ Spec (.of k)) → Prop}
    {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hX : X.HasFibreSatisfying B hZ P p) :
    Y.HasFibreSatisfying B hZ P
      (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p) := by
  obtain ⟨V, v, q, hV, hP⟩ := hX
  exact ⟨V, v, q ≫ φ.totalMap.hom, isPullback_comp_totalMap φ hV, hP⟩

/-- **Fibre conditions are insensitive to base change.** For a morphism `φ : X ⟶ Y` of families
of curves, the fibre of `X` at a field-valued point of its base satisfies `P` exactly when the
fibre of `Y` at the image point does. -/
theorem hasFibreSatisfying_map_iff
    {P : ∀ (k : Type u) [Field k] {V : Scheme.{u}}, (V ⟶ Spec (.of k)) → Prop}
    {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    Y.HasFibreSatisfying B hZ P
        (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p) ↔
      X.HasFibreSatisfying B hZ P p :=
  ⟨CurveFamily.hasFibreSatisfying_of_hom B hZ φ p, hasFibreSatisfying_map φ p⟩

/-! ### The genus of the fibres -/

/-- The fibre of a family of curves at a field-valued point `p` of its base *has genus `g`*: it
is presented by a scheme over the field of `p` whose genus, the dimension of the first
cohomology of its structure sheaf, is `g`. -/
abbrev HasGenusAt (X : CurveFamily B hZ)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) (g : ℕ) : Prop :=
  X.HasFibreSatisfying B hZ (fun _ _ _ f => genus f = g) p

/-- If the fibre at `p` has genus `g`, then every scheme presenting it has genus `g`. -/
theorem HasGenusAt.genus_eq {X : CurveFamily B hZ}
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj} {g : ℕ}
    (h : X.HasGenusAt p g) {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject)
    (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value)) :
    genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g := by
  obtain ⟨W, w, q', hW, rfl⟩ := h
  exact X.genus_eq_of_isPullback_of_isPullback w q' hW v q hV

/-- **The genus of a fibre is unique.** -/
theorem HasGenusAt.unique {X : CurveFamily B hZ}
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj} {g g' : ℕ}
    (h : X.HasGenusAt p g) (h' : X.HasGenusAt p g') : g = g' := by
  obtain ⟨V, v, q, hV, rfl⟩ := h
  exact h'.genus_eq v q hV

/-- **The genus of a fibre is invariant under extension of the field of the point**, in the
direction from a point to an extension of it at which the fibre is presented by a scheme. -/
theorem HasGenusAt.of_dominates {X : CurveFamily B hZ}
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj} {g : ℕ}
    (f : r.siteObject ⟶ p.siteObject) (hf : (schemeSpace X.base).obj.map f.op p.value = r.value)
    (h : X.HasGenusAt p g)
    (hr : ∃ (W : BigFppfOver B integerBase hZ) (w : W ⟶ r.siteObject)
      (q' : yoneda.obj W ⟶ X.total.obj),
        IsPullback q' (yoneda.map w) X.toBase.hom (yonedaEquiv.symm r.value)) :
    X.HasGenusAt r g := by
  obtain ⟨V, v, q, hV, rfl⟩ := h
  obtain ⟨W, w, q', hW⟩ := hr
  exact ⟨W, w, q', hW, X.genus_eq_of_dominates f hf v q hV w q' hW⟩

/-- **The genus of a fibre is invariant under extension of the field of the point**, in the
direction from an extension of a point to the point, when the fibre at the point is presented by
a scheme. -/
theorem HasGenusAt.of_dominated {X : CurveFamily B hZ}
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj} {g : ℕ}
    (f : r.siteObject ⟶ p.siteObject) (hf : (schemeSpace X.base).obj.map f.op p.value = r.value)
    (h : X.HasGenusAt r g)
    (hp : ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ X.total.obj),
        IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value)) :
    X.HasGenusAt p g := by
  obtain ⟨W, w, q', hW, rfl⟩ := h
  obtain ⟨V, v, q, hV⟩ := hp
  exact ⟨V, v, q, hV, (X.genus_eq_of_dominates f hf v q hV w q' hW).symm⟩

/-- **The genus of a fibre is insensitive to base change.** For a morphism of families of curves
`X ⟶ Y`, the fibre of `X` at a field-valued point of its base has genus `g` exactly when the fibre
of `Y` at the image point does: the two fibres are presented by the same schemes. -/
theorem hasGenusAt_map_iff {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) (g : ℕ) :
    Y.HasGenusAt (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p)
      g ↔ X.HasGenusAt p g :=
  hasFibreSatisfying_map_iff φ p

/-- All fibres of a family of curves *have genus `g`*: at every field-valued point of the base the
fibre is presented by a scheme of genus `g` over the field of the point. -/
def HasFibresOfGenus (X : CurveFamily B hZ) (g : ℕ) : Prop :=
  ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj, X.HasGenusAt p g

/-- **The genus-`g` condition pulls back.** For a morphism of families of curves `X ⟶ Y`, all
fibres of `X` have genus `g` exactly when the fibres of `Y` at the field-valued points of the base
of `Y` coming from the base of `X` have genus `g`. -/
theorem hasFibresOfGenus_iff_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y) (g : ℕ) :
    X.HasFibresOfGenus g ↔
      ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
        Y.HasGenusAt
          (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p) g :=
  forall_congr' fun p => (hasGenusAt_map_iff φ p g).symm

/-- A family of curves mapping to a family all of whose fibres have genus `g` has all its fibres
of genus `g`. -/
theorem HasFibresOfGenus.of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y) {g : ℕ}
    (h : Y.HasFibresOfGenus g) : X.HasFibresOfGenus g :=
  (hasFibresOfGenus_iff_of_hom φ g).2 fun _ => h _

/-- Over a base with a field-valued point, the genus of the fibres is unique. -/
theorem HasFibresOfGenus.unique {X : CurveFamily B hZ} {g g' : ℕ} (h : X.HasFibresOfGenus g)
    (h' : X.HasFibresOfGenus g')
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) : g = g' :=
  (h p).unique (h' p)

/-- The residue field of a point of the base of a family of curves, as a field-valued point of the
base. -/
noncomputable def residueFieldPoint (X : CurveFamily B hZ)
    (x : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj where
  carrier := X.base.left.1.residueField x
  contained := B.residueField_spec_contains X.base.left.2 x
  toBase := X.base.left.1.fromSpecResidueField x ≫ X.base.hom.1
  value := Space.residueFieldMap B integerBase hZ X.base x _


/-- The scheme point underlying the residue-field point of a point of the base is that point. -/
@[simp]
theorem schemePoint_residueFieldPoint (X : CurveFamily B hZ)
    (x : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    Space.schemePoint B integerBase hZ X.base (X.residueFieldPoint x) = x :=
  Scheme.fromSpecResidueField_apply _ _

/-- **The genus of a fibre depends only on the underlying point of the base.** If the fibres of a
family of curves are presented by schemes at every field-valued point of the base, then the
fibres at two field-valued points with the same underlying point of the base scheme have the same
genus: the two points have a common extension, and the genus is invariant under extension of the
field of the point. -/
theorem hasGenusAt_iff_of_schemePoint_eq {X : CurveFamily B hZ}
    (hfib : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ X.total.obj),
          IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    (h : Space.schemePoint B integerBase hZ X.base p = Space.schemePoint B integerBase hZ X.base r)
    (g : ℕ) : X.HasGenusAt p g ↔ X.HasGenusAt r g := by
  obtain ⟨s, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ :=
    Space.hasCommonExtension_of_schemePoint_eq B integerBase hZ X.base h
  exact ⟨fun hp => (hp.of_dominates f₁ hf₁ (hfib s)).of_dominated f₂ hf₂ (hfib r),
    fun hr => (hr.of_dominates f₂ hf₂ (hfib s)).of_dominated f₁ hf₁ (hfib p)⟩

/-- The *genus-`g` locus* of a family of curves: the set of points of the base at which the fibre
has genus `g`. -/
def genusLocus (X : CurveFamily B hZ) (g : ℕ) :
    Set ((BigFppfOver.toScheme B integerBase hZ).obj X.base) :=
  {x | X.HasGenusAt (X.residueFieldPoint x) g}

/-- When the fibres are presented by schemes, a field-valued point of the base lies over the
genus-`g` locus exactly when the fibre there has genus `g`. -/
theorem schemePoint_mem_genusLocus_iff {X : CurveFamily B hZ}
    (hfib : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ X.total.obj),
          IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) (g : ℕ) :
    Space.schemePoint B integerBase hZ X.base p ∈ X.genusLocus g ↔ X.HasGenusAt p g :=
  hasGenusAt_iff_of_schemePoint_eq hfib (by simp) g

/-- When the fibres are presented by schemes, all fibres have genus `g` exactly when the genus-`g`
locus is the whole base. -/
theorem hasFibresOfGenus_iff_genusLocus_eq_univ {X : CurveFamily B hZ}
    (hfib : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ X.total.obj),
          IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    (g : ℕ) : X.HasFibresOfGenus g ↔ X.genusLocus g = Set.univ := by
  refine ⟨fun h => Set.eq_univ_of_forall fun x => h _, fun h p => ?_⟩
  exact (schemePoint_mem_genusLocus_iff hfib p g).1 (h ▸ Set.mem_univ _)

/-- The genus loci for distinct genera are disjoint. -/
theorem disjoint_genusLocus (X : CurveFamily B hZ) {g g' : ℕ} (hg : g ≠ g') :
    Disjoint (X.genusLocus g) (X.genusLocus g') :=
  Set.disjoint_left.2 fun _ h h' => hg (HasGenusAt.unique h h')

/-- **The formation of the genus loci commutes with base change.** For a morphism of families of
curves `X ⟶ Y` such that the fibres of `Y` are presented by schemes, the genus-`g` locus of `X` is
the inverse image of the genus-`g` locus of `Y` along the morphism of bases. -/
theorem genusLocus_eq_preimage {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hfib : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ Y.total.obj),
          IsPullback q (yoneda.map v) Y.toBase.hom (yonedaEquiv.symm p.value))
    (g : ℕ) :
    X.genusLocus g =
      (BigFppfOver.toScheme B integerBase hZ).map φ.baseMap ⁻¹' Y.genusLocus g := by
  ext x
  show X.HasGenusAt _ g ↔ Y.HasGenusAt _ g
  rw [← hasGenusAt_map_iff φ]
  refine hasGenusAt_iff_of_schemePoint_eq hfib ?_ g
  rw [schemePoint_residueFieldPoint]
  exact (Space.schemePoint_map_yoneda B integerBase hZ φ.baseMap _).trans
    (congrArg _ (schemePoint_residueFieldPoint X x))

/-! ### Families of curves over a field -/

/-- The fibres of the family of curves of a morphism of schemes are presented by schemes: the
fibre product of the source with a field spectrum over the target. -/
theorem curveFamilyOfSchemeMorphism_exists_isPullback {T U : BigFppfOver B integerBase hZ}
    (g : T ⟶ U) (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace U).obj) :
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep
        hdim).total.obj),
        IsPullback q (yoneda.map v)
          (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase.hom
          (yonedaEquiv.symm p.value) :=
  ⟨pullback g p.value, pullback.snd _ _, yoneda.map (pullback.fst _ _),
    (IsPullback.of_hasPullback g p.value).map yoneda⟩

/-- **The genus of a fibre of the family of curves of a proper scheme over a field.** Let
`g : T ⟶ U` be a proper morphism of the big fppf site whose target is the spectrum of a field `k`.
Every scheme presenting the fibre of its family of curves at a field-valued point `p` has, over the
field of `p`, the genus of `T` over `k`: it is the base change of `T` along the field extension,
and genus is unchanged by extension of the ground field (Stacks 0BY9). -/
theorem genus_eq_of_isPullback_curveFamilyOfSchemeMorphism {T U : BigFppfOver B integerBase hZ}
    (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace U).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject)
    (q : yoneda.obj V ⟶ (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep
      hdim).total.obj)
    (hV : IsPullback q (yoneda.map v)
      (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase.hom
      (yonedaEquiv.symm p.value)) :
    genus ((BigFppfOver.toScheme B integerBase hZ).map v) =
      genus ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hU) := by
  set F := BigFppfOver.toScheme B integerBase hZ
  let pv : p.siteObject ⟶ U := p.value
  have hS₀ : IsPullback (F.map (Yoneda.fullyFaithful.preimage q)) (F.map v) (F.map g) (F.map pv) :=
    isPullback_toScheme_map_preimage hV
  have hS : IsPullback (F.map (Yoneda.fullyFaithful.preimage q)) (F.map v)
      (F.map g ≫ eqToHom hU) (F.map pv ≫ eqToHom hU) :=
    hS₀.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (eqToIso hU) (by simp) (by simp) (by simp) (by simp)
  have hφ : F.map pv ≫ eqToHom hU =
      Spec.map (CommRingCat.ofHom (Spec.preimage (F.map pv ≫ eqToHom hU)).hom) := by
    simp
  rw [hφ] at hS
  have : IsProper (F.map g ≫ eqToHom hU) := by
    have := hproper
    infer_instance
  exact genus_eq_of_isPullback k p.carrier _ _ _ _ hS

/-- **Clause (2) of Stacks 0E71, the genus.** Let `g : T ⟶ U` be a proper morphism of the big fppf
site whose target is the spectrum of a field `k` and whose source has dimension at most one. All
fibres of its family of curves have genus `n` exactly when `T` has genus `n` over `k`. -/
theorem hasFibresOfGenus_curveFamilyOfSchemeMorphism_iff {T U : BigFppfOver B integerBase hZ}
    (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) (n : ℕ) :
    (curveFamilyOfSchemeMorphism B hZ g
        (flat_of_eq_spec_field _ k hU) hproper
        (locallyOfFinitePresentation_of_eq_spec_field _ k hU)
        (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
        ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
        ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
        hdim).HasFibresOfGenus n ↔
      genus ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hU) = n := by
  refine ⟨fun h => ?_, fun h p => ?_⟩
  · obtain ⟨x⟩ : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj U) := by
      rw [hU]
      infer_instance
    obtain ⟨V, v, q, hV, hn⟩ := h (residueFieldPoint _ x)
    rw [← hn, genus_eq_of_isPullback_curveFamilyOfSchemeMorphism g k hU _ _ _ _ _ _ hdim _ v q hV]
  · obtain ⟨V, v, q, hV⟩ := curveFamilyOfSchemeMorphism_exists_isPullback g _ _ _ _ _ _ hdim p
    exact ⟨V, v, q, hV,
      (genus_eq_of_isPullback_curveFamilyOfSchemeMorphism g k hU _ _ _ _ _ _ hdim p v q hV).trans h⟩

end CurveFamily

/-! ### Semistable families of curves of genus `g` -/

/-- The fibres of a semistable family of curves are presented by schemes at every field-valued
point of the base. -/
theorem IsSemistableCurveFamily.exists_isPullback {X : CurveFamily B hZ}
    (hX : IsSemistableCurveFamily B hZ X)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ X.total.obj),
      IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) :=
  let ⟨V, v, q, hV, _⟩ := hX.2 p
  ⟨V, v, q, hV⟩

/-- The fibre of a semistable family of curves at a field-valued point of the base has positive
genus, and that genus is unique. -/
theorem IsSemistableCurveFamily.existsUnique_hasGenusAt {X : CurveFamily B hZ}
    (hX : IsSemistableCurveFamily B hZ X)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    ∃! g : ℕ, 1 ≤ g ∧ X.HasGenusAt p g := by
  obtain ⟨V, v, q, hV, hg, -⟩ := hX.2 p
  exact ⟨_, ⟨hg, V, v, q, hV, rfl⟩,
    fun g' hg' => CurveFamily.HasGenusAt.unique hg'.2 ⟨V, v, q, hV, rfl⟩⟩

/-- **The genus loci cover the base of a semistable family of curves**, with positive genera: every
point of the base lies in the genus-`g` locus for exactly one `g`, and that `g` is positive. -/
theorem IsSemistableCurveFamily.existsUnique_mem_genusLocus {X : CurveFamily B hZ}
    (hX : IsSemistableCurveFamily B hZ X)
    (x : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    ∃! g : ℕ, 1 ≤ g ∧ x ∈ X.genusLocus g :=
  IsSemistableCurveFamily.existsUnique_hasGenusAt hX (X.residueFieldPoint x)

/-- The genus-zero locus of a semistable family of curves is empty. -/
theorem IsSemistableCurveFamily.genusLocus_zero {X : CurveFamily B hZ}
    (hX : IsSemistableCurveFamily B hZ X) : X.genusLocus 0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨g, ⟨hg, hgx⟩, -⟩ := IsSemistableCurveFamily.existsUnique_mem_genusLocus hX x
  exact absurd (CurveFamily.HasGenusAt.unique hx hgx) (by omega)

/-- **The base of a semistable family of curves is the disjoint union of its genus loci of
positive genus.** -/
theorem IsSemistableCurveFamily.iUnion_genusLocus {X : CurveFamily B hZ}
    (hX : IsSemistableCurveFamily B hZ X) :
    ⋃ (g : ℕ) (_ : 1 ≤ g), X.genusLocus g = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    let ⟨g, ⟨hg, hx⟩, _⟩ := IsSemistableCurveFamily.existsUnique_mem_genusLocus hX x
    Set.mem_iUnion₂.2 ⟨g, hg, hx⟩


variable (B hZ) in
/-- A family of curves is *semistable of genus `g`* when it is semistable (Stacks 0E6Z) and all
its fibres have genus `g`. -/
abbrev IsSemistableCurveFamilyOfFibreGenus (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsSemistableCurveFamily B hZ X ∧ X.HasFibresOfGenus g

/-- A semistable family of curves of genus `g` is semistable. -/
theorem IsSemistableCurveFamilyOfFibreGenus.isSemistableCurveFamily {g : ℕ}
    {X : CurveFamily B hZ} (h : IsSemistableCurveFamilyOfFibreGenus B hZ g X) :
    IsSemistableCurveFamily B hZ X :=
  h.1

/-- A semistable family of curves has genus `g` exactly when its genus-`g` locus is the whole
base. -/
theorem isSemistableCurveFamilyOfFibreGenus_iff_genusLocus_eq_univ {g : ℕ}
    {X : CurveFamily B hZ} (hX : IsSemistableCurveFamily B hZ X) :
    IsSemistableCurveFamilyOfFibreGenus B hZ g X ↔ X.genusLocus g = Set.univ :=
  (and_iff_right hX).trans
    (CurveFamily.hasFibresOfGenus_iff_genusLocus_eq_univ
      (IsSemistableCurveFamily.exists_isPullback hX) g)

/-- **The genus of a semistable family of curves over a nonempty base is positive.** -/
theorem IsSemistableCurveFamilyOfFibreGenus.one_le {g : ℕ} {X : CurveFamily B hZ}
    (h : IsSemistableCurveFamilyOfFibreGenus B hZ g X)
    (x : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : 1 ≤ g := by
  obtain ⟨g', ⟨hg', hx⟩, -⟩ := IsSemistableCurveFamily.existsUnique_mem_genusLocus h.1 x
  exact (CurveFamily.HasGenusAt.unique (h.2 _) hx) ▸ hg'

/-- **The genus pieces are disjoint**: a semistable family of curves over a nonempty base has at
most one genus. -/
theorem IsSemistableCurveFamilyOfFibreGenus.unique {g g' : ℕ} {X : CurveFamily B hZ}
    (h : IsSemistableCurveFamilyOfFibreGenus B hZ g X)
    (h' : IsSemistableCurveFamilyOfFibreGenus B hZ g' X)
    (x : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : g = g' :=
  h.2.unique h'.2 (X.residueFieldPoint x)

/-- **The genus pieces cover the families over a one-point base**: a semistable family of curves
whose base has exactly one point — for instance the spectrum of a field — is semistable of a
unique genus, which is positive. -/
theorem IsSemistableCurveFamily.existsUnique_isSemistableCurveFamilyOfFibreGenus
    {X : CurveFamily B hZ} (hX : IsSemistableCurveFamily B hZ X)
    [Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj X.base)]
    [Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj X.base)] :
    ∃! g : ℕ, 1 ≤ g ∧ IsSemistableCurveFamilyOfFibreGenus B hZ g X := by
  obtain ⟨x⟩ := ‹Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj X.base)›
  obtain ⟨g, ⟨hg, hx⟩, -⟩ := IsSemistableCurveFamily.existsUnique_mem_genusLocus hX x
  have hg' : IsSemistableCurveFamilyOfFibreGenus B hZ g X :=
    (isSemistableCurveFamilyOfFibreGenus_iff_genusLocus_eq_univ hX).2
      (Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx)
  exact ⟨g, ⟨hg, hg'⟩, fun g' h' => (hg'.unique h'.2 x).symm⟩

/-- **Base change of the genus pieces.** A family of curves mapping to a semistable family `Y` is
semistable of genus `g` exactly when the morphism of bases lands in the genus-`g` locus of `Y`.
This is condition (o) of Section 0E0E for the genus-`g` piece, relative to the semistable
families, except for the openness of the locus. -/
theorem isSemistableCurveFamilyOfFibreGenus_iff_range_subset {g : ℕ} {X Y : CurveFamily B hZ}
    (φ : X ⟶ Y) (hY : IsSemistableCurveFamily B hZ Y) :
    IsSemistableCurveFamilyOfFibreGenus B hZ g X ↔
      Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ⊆ Y.genusLocus g := by
  have hX := CurveFamily.isSemistableCurveFamily_of_hom B hZ φ hY
  rw [isSemistableCurveFamilyOfFibreGenus_iff_genusLocus_eq_univ hX,
    CurveFamily.genusLocus_eq_preimage φ (IsSemistableCurveFamily.exists_isPullback hY),
    Set.range_subset_iff,
    Set.eq_univ_iff_forall]
  rfl

/-- A family of curves mapping to a semistable family of curves of genus `g` is semistable of
genus `g`. -/
theorem CurveFamily.isSemistableCurveFamilyOfFibreGenus_of_hom {g : ℕ} {X Y : CurveFamily B hZ}
    (φ : X ⟶ Y) (hY : IsSemistableCurveFamilyOfFibreGenus B hZ g Y) :
    IsSemistableCurveFamilyOfFibreGenus B hZ g X :=
  ⟨CurveFamily.isSemistableCurveFamily_of_hom B hZ φ hY.1, hY.2.of_hom φ⟩

variable (B hZ) in
/-- Being semistable of genus `g` is invariant under isomorphism of families of curves. -/
theorem curvesSemistableOfFibreGenus_isClosedUnderIsomorphisms (g : ℕ) :
    (show ObjectProperty (CurveFamily B hZ) from
      IsSemistableCurveFamilyOfFibreGenus B hZ g).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => CurveFamily.isSemistableCurveFamilyOfFibreGenus_of_hom e.inv hX⟩

variable (B hZ) in
/-- The strictly full subcategory `Curves^{semistable}_g` of semistable families of curves of
genus `g`. -/
abbrev CurvesSemistableOfFibreGenus (g : ℕ) :=
  (show ObjectProperty (CurveFamily B hZ) from
    IsSemistableCurveFamilyOfFibreGenus B hZ g).FullSubcategory

/-- **Clause (2) of Stacks 0E71 relative to Stacks 0E70.** Let `g : T ⟶ U` be a proper morphism of
the big fppf site whose target is the spectrum of a field `k` and whose source has dimension at
most one. Its family of curves is semistable of genus `n` exactly when it is semistable and `T`
has genus `n` over `k`. -/
theorem isSemistableCurveFamilyOfFibreGenus_curveFamilyOfSchemeMorphism_iff
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) (n : ℕ) :
    IsSemistableCurveFamilyOfFibreGenus B hZ n (curveFamilyOfSchemeMorphism B hZ g
        (flat_of_eq_spec_field _ k hU) hproper
        (locallyOfFinitePresentation_of_eq_spec_field _ k hU)
        (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
        ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
        ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim) ↔
      IsSemistableCurveFamily B hZ (curveFamilyOfSchemeMorphism B hZ g
        (flat_of_eq_spec_field _ k hU) hproper
        (locallyOfFinitePresentation_of_eq_spec_field _ k hU)
        (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
        ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
        ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim) ∧
        genus ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hU) = n :=
  and_congr_right' (CurveFamily.hasFibresOfGenus_curveFamilyOfSchemeMorphism_iff g k hU hproper
    hdim n)

end AlgebraicGeometry

end
