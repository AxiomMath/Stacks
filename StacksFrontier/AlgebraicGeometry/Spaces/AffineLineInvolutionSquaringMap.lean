module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionNotSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective

/-!
# The squaring map on the involution quotient is not separated

Let `k` be a field in which two is invertible, let `U = 𝐀¹_k`, let `R = Δ ⨿ Γ°` be the relation
scheme of Stacks 02Z1 and let `X = U/R` be its quotient. Squaring the coordinate descends to a
morphism `X ⟶ 𝐀¹_k`, the morphism `AlgebraicGeometry.AffineLineInvolution.squaringMap` of the
remark of Stacks 05VS. **It is not separated**, which is the last of the five assertions of that
remark and the point of it: a universally injective morphism of *schemes* is separated by
Stacks 05VE, so this is a universally injective morphism of algebraic spaces which is not.

## Main definitions

* `AlgebraicGeometry.AffineLineInvolution.relationChart` is the relation scheme of Stacks 02Z1
  as an object of a big fppf site containing `Spec k`, and
  `AlgebraicGeometry.AffineLineInvolution.squareFibreChart` is the fibre product of the
  squaring map of the affine line with itself, taken in that site.
* `AlgebraicGeometry.AffineLineInvolution.relationToSquareFibre` is the morphism
  `R ⟶ 𝐀¹_k ×_{𝐀¹_k} 𝐀¹_k` whose two components are the two projections of the relation.
* `AlgebraicGeometry.AffineLineInvolution.negSectionOver` is the section of that fibre product
  whose two components are the identity and negation.
* `AlgebraicGeometry.AffineLineInvolution.quotientChart` is the chart `h_U ⟶ X`.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.isPullback_quotientChart`: the relation is the kernel
  pair of the chart. This is the kernel-pair description of Stacks 02WW for the quotient sheaf
  of Stacks 02Z1.
* `AlgebraicGeometry.AffineLineInvolution.isPullback_diagonal_squaringMap`:
  `relationToSquareFibre` is a base change of the relative diagonal of the squaring map.
* `AlgebraicGeometry.AffineLineInvolution.not_isClosedImmersion_relationToSquareFibre`:
  `relationToSquareFibre` is not a closed immersion.
* `AlgebraicGeometry.AffineLineInvolution.not_isSeparated_squaringMap`: **part (5) of
  Stacks 05VS**, the squaring morphism on the involution quotient is not separated. This is
  also the closing assertion of the example of **Stacks 05Z6**, which is the same morphism
  `X ⟶ 𝐀¹_k` and the same statement about it.
* `CategoryTheory.Limits.isPullback_diagonal_of_isPullback` is the general categorical fact
  behind it: a kernel pair of `q : V ⟶ Z` is a base change of the relative diagonal of a
  morphism out of `Z`.
* `Stacks.Groupoids.isPullback_toQuotientSheaf_self`: a pre-relation whose two functors of
  points are sheaves is the kernel pair of the projection onto its quotient sheaf.

## Implementation notes

The non-separatedness needs no hypothesis on the quotient — in particular neither the
algebraic-space property nor the two effective-descent hypotheses of Stacks 0265 which
`AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient` carries. The
reason is that being separated is, by `AlgebraicGeometry.Space.IsSeparated`, a property of
*every* represented base change of the relative diagonal, so a single cartesian square
suffices to refute it, and the square exhibiting the relation as a base change of the diagonal
comes straight from the kernel-pair description of the quotient sheaf. Only
characteristic different from two is assumed, and only because the relation is an equivalence
relation for no other field.

The relation of Stacks 02Z1 is a pre-relation in `CategoryTheory.Over (Spec k)` rather than a
pair of morphisms of the site, so the first step is to name an object of the site whose
underlying `Spec k`-scheme is *literally* the relation scheme; the size bound is
`AlgebraicGeometry.BigFppfSite.contains_coprod` together with
`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion` for the punctured line. The two
projections of the relation and the squaring map are then preimages under the fully faithful
`CategoryTheory.Over.post AlgebraicGeometry.BigFppfSite.inclusion`, and the fibre product and
the comparison `relationToSquareFibre` are formed in the site itself.

Each morphism of the site used here is therefore accompanied by a named `…Over` version of its
image in `CategoryTheory.Over (Spec k)`. This is bookkeeping, not mathematics, and it is worth
saying why it is needed: `CategoryTheory.Over.post B.inclusion` has target
`CategoryTheory.Over (B.inclusion.obj (B.obj hk))`, which is only *definitionally* the category
`CategoryTheory.Over (Spec k)` in which the relation lives, and a rewrite whose two sides are
typed in different spellings of one category is rejected. Giving each image morphism a
declared type in `CategoryTheory.Over (Spec k)` fixes one spelling, after which the identities
of Stacks 02Z1 may be rewritten in the usual way; passing between the two spellings happens
only in proofs closed by `exact`, where definitional equality is available. Identifying a fibre
product of the site with the fibre product of the images uses that
`CategoryTheory.Over.post B.inclusion` preserves fibre products, which follows from
`AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme` because
`CategoryTheory.Over.forget` reflects connected limits.

The geometry enters through `negSectionOver`. It is split by the first projection, hence a
separated morphism on underlying schemes, and on the second summand of `R` the comparison
`relationToSquareFibre` is the inclusion of the puncture followed by it; so
`AlgebraicGeometry.AffineLineInvolution.not_isClosedImmersion_of_inr_left_comp_eq` applies. No
morphism to `𝐀¹_k ×_k 𝐀¹_k` is needed, and in particular the closed-immersion property of
`𝐀¹_k ×_{𝐀¹_k} 𝐀¹_k ⟶ 𝐀¹_k ×_k 𝐀¹_k` is never used.

The chart `h_U ⟶ X` is the projection to the quotient sheaf read through
`AlgebraicGeometry.Space.pointsYonedaIso`, and the identification of the two maps across that
isomorphism is `AlgebraicGeometry.Space.pointsYonedaIso_inv_comp_whiskerLeft`. The kernel-pair
square is `AlgebraicGeometry.Space.quotientPresheaf_isPullback` followed by sheafification,
which is left exact, the two outer vertices being sheaves already.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 05VE](https://stacks.math.columbia.edu/tag/05VE)
* [Stacks Project, Tag 05VS](https://stacks.math.columbia.edu/tag/05VS)
* [Stacks Project, Tag 05Z6](https://stacks.math.columbia.edu/tag/05Z6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Limits

/-- A kernel pair of `q : V ⟶ Z` is a base change of the relative diagonal of `f : Z ⟶ Y`: if
`π₁, π₂ : W ⟶ V` is a jointly monic pair whose composites with `q ≫ f` agree and `j : R ⟶ W`
has components the two legs `a, b : R ⟶ V` of the kernel pair, then `j` is the base change of
`CategoryTheory.Limits.pullback.diagonal f` along the map `W ⟶ Z ×_Y Z` with components
`π₁ ≫ q` and `π₂ ≫ q`.

This is the relative counterpart of
`CategoryTheory.Limits.isPullback_diag_of_isPullback`, which is the same statement for the
absolute diagonal `Z ⟶ Z ⨯ Z`. -/
theorem isPullback_diagonal_of_isPullback {C : Type v} [Category.{w} C]
    {Y Z V R W : C} {f : Z ⟶ Y} [HasPullback f f] {q : V ⟶ Z}
    {a b : R ⟶ V} (hab : IsPullback a b q q)
    {π₁ π₂ : W ⟶ V} {j : R ⟶ W} (h₁ : j ≫ π₁ = a) (h₂ : j ≫ π₂ = b)
    (hW : ∀ {T : C} (u v : T ⟶ W), u ≫ π₁ = v ≫ π₁ → u ≫ π₂ = v ≫ π₂ → u = v)
    (hq : (π₁ ≫ q) ≫ f = (π₂ ≫ q) ≫ f) :
    IsPullback (a ≫ q) j (pullback.diagonal f)
      (pullback.lift (π₁ ≫ q) (π₂ ≫ q) hq) := by
  have key : ∀ (T : C) (u : T ⟶ Z) (v : T ⟶ W),
      u ≫ pullback.diagonal f = v ≫ pullback.lift (π₁ ≫ q) (π₂ ≫ q) hq →
      u = (v ≫ π₁) ≫ q ∧ u = (v ≫ π₂) ≫ q := by
    intro T u v h
    refine ⟨?_, ?_⟩
    · simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
        pullback.lift_fst] using congrArg (· ≫ pullback.fst f f) h
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id,
        pullback.lift_snd] using congrArg (· ≫ pullback.snd f f) h
  have hcomm : CommSq (a ≫ q) j (pullback.diagonal f)
      (pullback.lift (π₁ ≫ q) (π₂ ≫ q) hq) := by
    refine ⟨pullback.hom_ext ?_ ?_⟩
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst]
      rw [← Category.assoc, h₁]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd]
      rw [← Category.assoc, h₂, hab.w]
  refine IsPullback.of_isLimit' hcomm (PullbackCone.IsLimit.mk hcomm.w
    (fun c => hab.lift (c.snd ≫ π₁) (c.snd ≫ π₂) ?_) ?_ ?_ ?_)
  · obtain ⟨e₁, e₂⟩ := key _ c.fst c.snd c.condition
    rw [← e₁, ← e₂]
  · intro c
    obtain ⟨e₁, -⟩ := key _ c.fst c.snd c.condition
    rw [← Category.assoc, hab.lift_fst, ← e₁]
  · intro c
    refine hW _ _ ?_ ?_
    · rw [Category.assoc, h₁, hab.lift_fst]
    · rw [Category.assoc, h₂, hab.lift_snd]
  · intro c m _ hm₂
    refine hab.hom_ext ?_ ?_
    · rw [hab.lift_fst, ← h₁, ← Category.assoc, hm₂]
    · rw [hab.lift_snd, ← h₂, ← Category.assoc, hm₂]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

/-- The identity section of the restricted functor of points of `F.obj U`, read through the
Yoneda correspondence, is the inverse of `AlgebraicGeometry.Space.pointsYonedaIso`. -/
theorem pointsYonedaIso_inv_eq {C : Type v} [Category.{u} C] {S : Scheme.{u}}
    (F : C ⥤ Over S) [F.Full] [F.Faithful] (U : C) :
    (yonedaEquiv (F := Stacks.Groupoids.points F (F.obj U))).symm (𝟙 (F.obj U)) =
      (pointsYonedaIso F U).inv := by
  apply (yonedaEquiv (F := Stacks.Groupoids.points F (F.obj U))).injective
  simp [pointsYonedaIso, Stacks.Groupoids.points, Functor.FullyFaithful.homEquiv,
    Functor.FullyFaithful.ofFullyFaithful, yonedaEquiv]


/-- Composition with a morphism between `F`-images, read on restricted functors of points, is
`CategoryTheory.yoneda` of its preimage across
`AlgebraicGeometry.Space.pointsYonedaIso`. -/
theorem pointsYonedaIso_inv_comp_whiskerLeft {C : Type v} [Category.{u} C] {S : Scheme.{u}}
    (F : C ⥤ Over S) [F.Full] [F.Faithful] {V W : C} (g : F.obj V ⟶ F.obj W) :
    (pointsYonedaIso F V).inv ≫ F.op.whiskerLeft (yoneda.map g) =
      yoneda.map (F.preimage g) ≫ (pointsYonedaIso F W).inv := by
  ext X h
  change F.map h ≫ g = F.map (h ≫ F.preimage g)
  rw [F.map_comp, F.map_preimage]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-! ### The relation scheme as an object of the site -/

include hk in
/-- The relation scheme of Stacks 02Z1 satisfies the size cutoff of a big fppf site containing
`Spec k`: it is the coproduct of the affine line and of an open subscheme of it. -/
theorem contains_relationScheme : B.Contains (relationScheme k).left :=
  lt_of_eq_of_lt
    (Scheme.size_congr (overCoprodIso (affineLine k) (puncturedAffineLine k))).symm
    (B.contains_coprod (affineLineChart k B hk).left.property
      (Scheme.size_lt_of_isOpenImmersion (puncturedAffineLineOpen k).ι
        (affineLineChart k B hk).left.property))

/-- **Stacks 02Z1.** The relation scheme, as an object of a big fppf site containing
`Spec k`. -/
noncomputable def relationChart : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (ObjectProperty.homMk (relationScheme k).hom :
    B.obj (contains_relationScheme k B hk) ⟶ B.obj hk)

/-- The image of `relationChart` in `Spec k`-schemes is the relation scheme. -/
@[simp]
theorem relationChart_post :
    (Over.post B.inclusion).obj (relationChart k B hk) = relationScheme k := rfl

/-! ### The fibre square of the squaring map -/

/-- Squaring the coordinate of the affine line, as a morphism of the site. -/
noncomputable def affineLineSquareChart : affineLineChart k B hk ⟶ affineLineChart k B hk :=
  (Over.post B.inclusion).preimage
    (X := affineLineChart k B hk) (Y := affineLineChart k B hk) (affineLineSquare k)

/-- Squaring the coordinate of the affine line, as the image of a morphism of the site. -/
noncomputable def affineLineSquareOver : affineLine k ⟶ affineLine k :=
  (Over.post B.inclusion).map (affineLineSquareChart k B hk)

/-- `affineLineSquareOver` is the squaring map `affineLineSquare` of the affine line. -/
theorem affineLineSquareOver_eq : affineLineSquareOver k B hk = affineLineSquare k :=
  (Over.post B.inclusion).map_preimage _

/-- The fibre product of the squaring map of the affine line with itself, taken in the
site. -/
noncomputable abbrev squareFibreChart : BigFppfOver B (Spec (.of k)) hk :=
  Limits.pullback (affineLineSquareChart k B hk) (affineLineSquareChart k B hk)

/-- The fibre product of the squaring map with itself, as a `Spec k`-scheme. -/
noncomputable def squareFibreOver : Over (Spec (.of k)) :=
  (Over.post B.inclusion).obj (squareFibreChart k B hk)

/-- The first projection of the fibre square, as a morphism of `Spec k`-schemes. -/
noncomputable def squareFibreFstOver : squareFibreOver k B hk ⟶ affineLine k :=
  (Over.post B.inclusion).map
    (pullback.fst (affineLineSquareChart k B hk) (affineLineSquareChart k B hk))

/-- The second projection of the fibre square, as a morphism of `Spec k`-schemes. -/
noncomputable def squareFibreSndOver : squareFibreOver k B hk ⟶ affineLine k :=
  (Over.post B.inclusion).map
    (pullback.snd (affineLineSquareChart k B hk) (affineLineSquareChart k B hk))

/-- The fibre square of the squaring map, read in the category of `Spec k`-schemes. The
functor from the site preserves fibre products, being
`CategoryTheory.Over.post` of the inclusion of the size-bounded schemes. -/
theorem isPullback_squareFibreOver :
    IsPullback (squareFibreFstOver k B hk) (squareFibreSndOver k B hk)
      (affineLineSquareOver k B hk) (affineLineSquareOver k B hk) := by
  have hpres : PreservesLimitsOfShape WalkingCospan
      (Over.post (X := B.obj hk) B.inclusion ⋙ Over.forget (Spec (.of k))) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B (Spec (.of k)) hk
  have : PreservesLimitsOfShape WalkingCospan (Over.post (X := B.obj hk) B.inclusion) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget (Spec (.of k)))
  exact (IsPullback.of_hasPullback (affineLineSquareChart k B hk)
    (affineLineSquareChart k B hk)).map (Over.post B.inclusion)

/-! ### The relation as a morphism into the fibre square -/

/-- The first projection of the relation of Stacks 02Z1, as a morphism of the site. -/
noncomputable def relationTarget : relationChart k B hk ⟶ affineLineChart k B hk :=
  (Over.post B.inclusion).preimage
    (X := relationChart k B hk) (Y := affineLineChart k B hk) (involutionRelation k).target

/-- The second projection of the relation of Stacks 02Z1, as a morphism of the site. -/
noncomputable def relationSource : relationChart k B hk ⟶ affineLineChart k B hk :=
  (Over.post B.inclusion).preimage
    (X := relationChart k B hk) (Y := affineLineChart k B hk) (involutionRelation k).source

/-- The first projection of the relation, as the image of a morphism of the site. -/
noncomputable def relationTargetOver : relationScheme k ⟶ affineLine k :=
  (Over.post B.inclusion).map (relationTarget k B hk)

/-- The second projection of the relation, as the image of a morphism of the site. -/
noncomputable def relationSourceOver : relationScheme k ⟶ affineLine k :=
  (Over.post B.inclusion).map (relationSource k B hk)

/-- `relationTargetOver` is the target projection of the involution relation. -/
theorem relationTargetOver_eq :
    relationTargetOver k B hk = (involutionRelation k).target :=
  (Over.post B.inclusion).map_preimage _

/-- `relationSourceOver` is the source projection of the involution relation. -/
theorem relationSourceOver_eq :
    relationSourceOver k B hk = (involutionRelation k).source :=
  (Over.post B.inclusion).map_preimage _

/-- The two projections of the relation have the same square in the site. -/
theorem relationTarget_comp_affineLineSquareChart :
    relationTarget k B hk ≫ affineLineSquareChart k B hk =
      relationSource k B hk ≫ affineLineSquareChart k B hk := by
  apply (Over.post B.inclusion).map_injective
  have h : relationTargetOver k B hk ≫ affineLineSquareOver k B hk =
      relationSourceOver k B hk ≫ affineLineSquareOver k B hk := by
    rw [relationTargetOver_eq, relationSourceOver_eq, affineLineSquareOver_eq]
    exact (involutionRelation_source_comp_affineLineSquare k).symm
  exact ((Over.post B.inclusion).map_comp _ _).trans
    (h.trans ((Over.post B.inclusion).map_comp _ _).symm)

/-- **Stacks 02Z1.** The relation, as a morphism of the site into the fibre square of the
squaring map: its two components are the two projections of the relation, which have the same
square. -/
noncomputable def relationToSquareFibre : relationChart k B hk ⟶ squareFibreChart k B hk :=
  pullback.lift (relationTarget k B hk) (relationSource k B hk)
    (relationTarget_comp_affineLineSquareChart k B hk)

/-- The first component of `relationToSquareFibre` is `relationTarget`. -/
@[simp]
theorem relationToSquareFibre_comp_fst :
    relationToSquareFibre k B hk ≫
        pullback.fst (affineLineSquareChart k B hk) (affineLineSquareChart k B hk) =
      relationTarget k B hk :=
  pullback.lift_fst _ _ _

/-- The second component of `relationToSquareFibre` is `relationSource`. -/
@[simp]
theorem relationToSquareFibre_comp_snd :
    relationToSquareFibre k B hk ≫
        pullback.snd (affineLineSquareChart k B hk) (affineLineSquareChart k B hk) =
      relationSource k B hk :=
  pullback.lift_snd _ _ _

/-- The relation into the fibre square, as a morphism of `Spec k`-schemes. -/
noncomputable def relationToSquareFibreOver :
    relationScheme k ⟶ squareFibreOver k B hk :=
  (Over.post B.inclusion).map (relationToSquareFibre k B hk)

/-- The first component of `relationToSquareFibreOver` is the target projection of the
involution relation. -/
theorem relationToSquareFibreOver_comp_fst :
    relationToSquareFibreOver k B hk ≫ squareFibreFstOver k B hk =
      (involutionRelation k).target :=
  ((Over.post B.inclusion).map_comp _ _).symm.trans
    ((congrArg _ (relationToSquareFibre_comp_fst k B hk)).trans (relationTargetOver_eq k B hk))

/-- The second component of `relationToSquareFibreOver` is the source projection of the
involution relation. -/
theorem relationToSquareFibreOver_comp_snd :
    relationToSquareFibreOver k B hk ≫ squareFibreSndOver k B hk =
      (involutionRelation k).source :=
  ((Over.post B.inclusion).map_comp _ _).symm.trans
    ((congrArg _ (relationToSquareFibre_comp_snd k B hk)).trans (relationSourceOver_eq k B hk))

/-! ### The negation section of the fibre square -/

/-- The section of the fibre square of the squaring map whose two components are the identity
and negation: squaring the coordinate is unchanged by negating it. -/
noncomputable def negSectionOver : affineLine k ⟶ squareFibreOver k B hk :=
  (isPullback_squareFibreOver k B hk).lift (𝟙 (affineLine k)) (affineLineNeg k)
    (by rw [affineLineSquareOver_eq, Category.id_comp, affineLineNeg_comp_affineLineSquare])

/-- The first component of `negSectionOver` is the identity of the affine line. -/
theorem negSectionOver_comp_fst :
    negSectionOver k B hk ≫ squareFibreFstOver k B hk = 𝟙 (affineLine k) :=
  (isPullback_squareFibreOver k B hk).lift_fst _ _ _

/-- The second component of `negSectionOver` is the negation `affineLineNeg`. -/
theorem negSectionOver_comp_snd :
    negSectionOver k B hk ≫ squareFibreSndOver k B hk = affineLineNeg k :=
  (isPullback_squareFibreOver k B hk).lift_snd _ _ _

/-- The negation section is a split monomorphism on underlying schemes, retracted by the first
projection. -/
theorem isSplitMono_negSectionOver_left : IsSplitMono ((negSectionOver k B hk).left) :=
  ⟨⟨{ retraction := (squareFibreFstOver k B hk).left
      id := congrArg Over.Hom.left (negSectionOver_comp_fst k B hk) }⟩⟩

/-- On the second summand of the relation scheme the comparison into the fibre square is the
inclusion of the punctured affine line followed by the negation section. -/
theorem inr_comp_relationToSquareFibreOver :
    (coprod.inr : puncturedAffineLine k ⟶ relationScheme k) ≫
        relationToSquareFibreOver k B hk =
      puncturedAffineLineInclusion k ≫ negSectionOver k B hk := by
  refine (isPullback_squareFibreOver k B hk).hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, relationToSquareFibreOver_comp_fst,
      negSectionOver_comp_fst, Category.comp_id, involutionRelation_target, coprod.inr_desc]
  · rw [Category.assoc, Category.assoc, relationToSquareFibreOver_comp_snd,
      negSectionOver_comp_snd, involutionRelation_source, coprod.inr_desc]

/-- **The relation of Stacks 02Z1 is not a closed immersion into the fibre square of the
squaring map.** Its restriction to the second summand factors through the negation section,
which is a split monomorphism, hence separated. -/
theorem not_isClosedImmersion_relationToSquareFibre :
    ¬ IsClosedImmersion ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (relationToSquareFibre k B hk)) := by
  have hmono : Mono ((negSectionOver k B hk).left) :=
    (isSplitMono_negSectionOver_left k B hk).mono
  have hsep : IsSeparated ((negSectionOver k B hk).left) := inferInstance
  exact not_isClosedImmersion_of_inr_left_comp_eq k
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (relationToSquareFibre k B hk))
    ((negSectionOver k B hk).left) hsep
    (congrArg Over.Hom.left (inr_comp_relationToSquareFibreOver k B hk))

/-! ### The chart of the involution quotient -/

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-- The restricted functor of points of the affine line is the presheaf represented by its
chart. -/
noncomputable def affineLinePointsIso :
    Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k) ≅
      yoneda.obj (affineLineChart k B hk) :=
  Space.pointsYonedaIso (Over.post B.inclusion) (affineLineChart k B hk)

/-- The restricted functor of points of the relation scheme is the presheaf represented by its
chart. -/
noncomputable def relationPointsIso :
    Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (relationScheme k) ≅
      yoneda.obj (relationChart k B hk) :=
  Space.pointsYonedaIso (Over.post B.inclusion) (relationChart k B hk)

/-- The chart of the involution quotient: the projection of the affine line onto the quotient
sheaf of Stacks 02WW, read on the presheaf represented by the affine line. -/
noncomputable def quotientChart :
    yoneda.obj (affineLineChart k B hk) ⟶ (involutionQuotient k B hk).obj :=
  (affineLinePointsIso k B hk).inv ≫
    Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
      (Over.post B.inclusion) (involutionRelation k)

/-- The relation of Stacks 02Z1 is the kernel pair of the chart of its quotient. This is the
kernel-pair description of Stacks 02WW for the quotient sheaf of that example. -/
theorem isPullback_quotientChart (hchar : (2 : k) ≠ 0) :
    IsPullback (yoneda.map (relationTarget k B hk)) (yoneda.map (relationSource k B hk))
      (quotientChart k B hk) (quotientChart k B hk) := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have hsheaf := Stacks.Groupoids.isPullback_toQuotientSheaf_self
    (BigFppfOver.topology B (Spec (.of k)) hk) (Over.post (X := B.obj hk) B.inclusion)
    (involutionRelation k)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (Spec (.of k)) hk
      (relationScheme k))
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (Spec (.of k)) hk (affineLine k))
  refine hsheaf.of_iso' (relationPointsIso k B hk).symm (affineLinePointsIso k B hk).symm
    (affineLinePointsIso k B hk).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · exact Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post B.inclusion)
      (V := relationChart k B hk) (W := affineLineChart k B hk) _
  · exact Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post B.inclusion)
      (V := relationChart k B hk) (W := affineLineChart k B hk) _
  all_goals exact (Category.comp_id _).symm

/-- The chart composed with the squaring map is squaring the coordinate of the affine line. -/
theorem quotientChart_comp_squaringMap :
    quotientChart k B hk ≫ squaringMap k B hk =
      yoneda.map (affineLineSquareChart k B hk) ≫ (affineLinePointsIso k B hk).inv := by
  have hassoc : quotientChart k B hk ≫ squaringMap k B hk =
      (affineLinePointsIso k B hk).inv ≫
        (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post B.inclusion) (involutionRelation k) ≫ squaringMap k B hk) :=
    Category.assoc _ _ _
  rw [hassoc, toQuotientSheaf_comp_squaringMap]
  exact Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post B.inclusion)
    (V := affineLineChart k B hk) (W := affineLineChart k B hk) (affineLineSquare k)

/-! ### The fifth assertion of Stacks 05VS -/

/-- The two projections of the fibre square have the same composite with the chart followed by
the squaring map. -/
theorem squareFibre_comp_quotientChart_comp_squaringMap :
    (yoneda.map (pullback.fst (affineLineSquareChart k B hk) (affineLineSquareChart k B hk)) ≫
        quotientChart k B hk) ≫ squaringMap k B hk =
      (yoneda.map (pullback.snd (affineLineSquareChart k B hk)
        (affineLineSquareChart k B hk)) ≫ quotientChart k B hk) ≫ squaringMap k B hk := by
  rw [Category.assoc, Category.assoc, quotientChart_comp_squaringMap, ← Category.assoc,
    ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the pullbacks of presheaves in this statement is heavy
/-- **The relation of Stacks 02Z1 is a base change of the relative diagonal of the squaring
map.** The chart of the quotient has the relation as its kernel pair, and the two projections
of the fibre square of the squaring map are jointly monic. -/
theorem isPullback_diagonal_squaringMap (hchar : (2 : k) ≠ 0) :
    IsPullback (yoneda.map (relationTarget k B hk) ≫ quotientChart k B hk)
      (yoneda.map (relationToSquareFibre k B hk))
      (pullback.diagonal (squaringMap k B hk))
      (pullback.lift
        (yoneda.map (pullback.fst (affineLineSquareChart k B hk)
          (affineLineSquareChart k B hk)) ≫ quotientChart k B hk)
        (yoneda.map (pullback.snd (affineLineSquareChart k B hk)
          (affineLineSquareChart k B hk)) ≫ quotientChart k B hk)
        (squareFibre_comp_quotientChart_comp_squaringMap k B hk)) := by
  have hsq := yoneda.map_isPullback (IsPullback.of_hasPullback
    (affineLineSquareChart k B hk) (affineLineSquareChart k B hk))
  refine isPullback_diagonal_of_isPullback (isPullback_quotientChart k B hk hchar) ?_ ?_
    (fun u v hu hv => hsq.hom_ext hu hv) _
  · rw [← yoneda.map_comp, relationToSquareFibre_comp_fst]
  · rw [← yoneda.map_comp, relationToSquareFibre_comp_snd]

/-- **Stacks 05VS, part (5)**, which is also the last assertion of the example of **Stacks
05Z6**: the squaring map `X ⟶ 𝐀¹_k` on the involution quotient is not separated. Its relative
diagonal has the relation of Stacks 02Z1 as a represented base change, and that relation is
not a closed immersion. -/
@[stacks 05VS "part (5): the squaring morphism is not separated"]
theorem not_isSeparated_squaringMap (hchar : (2 : k) ≠ 0) :
    ¬ Space.IsSeparated B (Spec (.of k)) hk (squaringMap k B hk) := by
  intro hsep
  exact not_isClosedImmersion_relationToSquareFibre k B hk
    (hsep.property _ _ (relationToSquareFibre k B hk)
      (isPullback_diagonal_squaringMap k B hk hchar))

end AlgebraicGeometry.AffineLineInvolution

end
