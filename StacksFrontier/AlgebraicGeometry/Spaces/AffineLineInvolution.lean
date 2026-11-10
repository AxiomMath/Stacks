module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf

/-!
# The affine line with its nonzero points identified with their negatives

Stacks 02Z1 is the example of an algebraic space which is quasi-separated but not locally
separated: over a field `k` of characteristic different from two, let `U = 𝔸¹_k`, let
`R = Δ ⨿ Γ` where `Δ` is the diagonal of `U` and `Γ` is the graph of negation on the
punctured line, and let `X = U/R`.  This file constructs `U`, `R`, the relation
`j : R ⟶ U ×_k U` and the quotient sheaf `X`, and proves the geometric facts about them on
which the assertions of the example rest: the two projections of `R` are étale and affine,
and `U` is affine over `k`.

## Main definitions

* `AlgebraicGeometry.AffineLineInvolution.affineLine` is `𝔸¹_k` as a scheme over `Spec k`.
* `AlgebraicGeometry.AffineLineInvolution.puncturedAffineLine` is the basic open of the
  standard coordinate, with `puncturedAffineLineInclusion` its inclusion.
* `AlgebraicGeometry.AffineLineInvolution.affineLineNeg` negates the coordinate.
* `AlgebraicGeometry.AffineLineInvolution.relationScheme` is `𝔸¹_k ⨿ (𝔸¹_k ∖ 0)` and
  `AlgebraicGeometry.AffineLineInvolution.involutionRelation` is the pre-relation which is
  the diagonal on the first summand and the graph of negation on the second.
* `AlgebraicGeometry.AffineLineInvolution.involutionQuotient` is its fppf quotient sheaf.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.isIso_affineLineNeg`: negation is an involution,
  hence an isomorphism.
* `AlgebraicGeometry.AffineLineInvolution.etale_target` and
  `AlgebraicGeometry.AffineLineInvolution.etale_source`: the two projections `R ⟶ U` are
  étale.
* `AlgebraicGeometry.AffineLineInvolution.isAffineHom_target`,
  `AlgebraicGeometry.AffineLineInvolution.isAffineHom_source` and
  `AlgebraicGeometry.AffineLineInvolution.quasiCompact_source`: the two projections are
  affine, and the second is quasi-compact.
* `AlgebraicGeometry.AffineLineInvolution.quasiSeparated_affineLine`: `U ⟶ Spec k` is
  quasi-separated.

## Implementation notes

The coordinate of the affine line is indexed by a singleton, and the relation is assembled
from the binary product and coproduct of `CategoryTheory.Over (Spec k)`.  Coproducts there
are computed on underlying schemes, so `left_coprod_desc` transfers a morphism property
from `coprod.desc` of the underlying morphisms to the underlying morphism of `coprod.desc`.

The constructions themselves make sense in every characteristic; characteristic different
from two is needed only for the geometric assertions of the example about the quotient, and
so appears in no statement here.

## References

* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Coproducts of schemes over a base

Binary coproducts in `CategoryTheory.Over S` are created by `CategoryTheory.Over.forget`, so
the underlying morphism of a map out of a coproduct is, up to the comparison isomorphism, the
corresponding map out of the coproduct of the underlying schemes. -/

/-- The underlying morphism of `coprod.desc` in `CategoryTheory.Over S`, composed with the
comparison isomorphism, is `coprod.desc` of the underlying morphisms. -/
theorem coprodComparison_comp_left_coprod_desc {S : Scheme.{u}} {X Y Z : Over S}
    (a : X ⟶ Z) (b : Y ⟶ Z) :
    coprodComparison (Over.forget S) X Y ≫ (coprod.desc a b : X ⨿ Y ⟶ Z).left
      = coprod.desc a.left b.left := by
  refine coprod.hom_ext ?_ ?_
  · simp only [coprodComparison, coprod.inl_desc_assoc, coprod.inl_desc]
    change ((coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.desc a b).left = _
    rw [coprod.inl_desc]
  · simp only [coprodComparison, coprod.inr_desc_assoc, coprod.inr_desc]
    change ((coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.desc a b).left = _
    rw [coprod.inr_desc]

/-- A morphism property which respects isomorphisms holds for the underlying morphism of
`coprod.desc` in `CategoryTheory.Over S` as soon as it holds for `coprod.desc` of the
underlying morphisms. -/
theorem left_coprod_desc {S : Scheme.{u}} {X Y Z : Over S}
    (P : MorphismProperty Scheme.{u}) (hP : P.RespectsIso) (a : X ⟶ Z) (b : Y ⟶ Z)
    (h : P (coprod.desc a.left b.left)) : P (coprod.desc a b : X ⨿ Y ⟶ Z).left := by
  rw [← coprodComparison_comp_left_coprod_desc a b] at h
  have : IsIso (coprodComparison (Over.forget S) X Y) :=
    (PreservesColimitPair.iso (Over.forget S) X Y).isIso_hom
  exact (MorphismProperty.cancel_left_of_respectsIso (P := P)
    (coprodComparison (Over.forget S) X Y) _).mp h

/-- A property local at the source and respecting isomorphisms holds for `coprod.desc` of two
morphisms of schemes as soon as it holds for each of them.  This is the binary case of
`AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc`. -/
theorem property_coprod_desc {X Y Z : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    (hP : P.RespectsIso) (hloc : IsZariskiLocalAtSource P) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : P f) (hg : P g) : P (coprod.desc f g) := by
  have hd : P (Sigma.desc (fun i : ULift.{u} WalkingPair =>
      i.1.casesOn (motive := fun j => (j.casesOn X Y : Scheme.{u}) ⟶ Z) f g)) :=
    IsZariskiLocalAtSource.sigmaDesc (fun i => by
      obtain ⟨i⟩ := i; cases i <;> assumption)
  have he : (coprodIsoSigma X Y).hom ≫ Sigma.desc (fun i : ULift.{u} WalkingPair =>
      i.1.casesOn (motive := fun j => (j.casesOn X Y : Scheme.{u}) ⟶ Z) f g)
      = coprod.desc f g := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, ← ι_left_coprodIsoSigma_inv, Category.assoc,
        Iso.inv_hom_id_assoc, colimit.ι_desc]
      rfl
    · rw [coprod.inr_desc, ← ι_right_coprodIsoSigma_inv, Category.assoc,
        Iso.inv_hom_id_assoc, colimit.ι_desc]
      rfl
  rw [← he]
  exact MorphismProperty.RespectsIso.precomp _ (coprodIsoSigma X Y).hom _ hd

namespace AffineLineInvolution

variable (k : Type u) [Field k]

/-- The affine line over `Spec k`, the chart of the example. -/
@[stacks 02Z1 "the chart 𝔸¹"]
noncomputable abbrev affineLine : Over (Spec (.of k)) :=
  Over.mk ((AffineSpace PUnit.{u + 1} (Spec (.of k))) ↘ Spec (.of k))

/-- The basic open of the standard coordinate, the punctured affine line. -/
@[stacks 02Z1 "the punctured line, as an open"]
noncomputable abbrev puncturedAffineLineOpen : (affineLine k).left.Opens :=
  (affineLine k).left.basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit)

/-- The punctured affine line as a scheme over `Spec k`. -/
@[stacks 02Z1 "the punctured line"]
noncomputable abbrev puncturedAffineLine : Over (Spec (.of k)) :=
  Over.mk ((puncturedAffineLineOpen k).ι ≫ (affineLine k).hom)

/-- The inclusion of the punctured affine line into the affine line. -/
noncomputable def puncturedAffineLineInclusion :
    puncturedAffineLine k ⟶ affineLine k :=
  Over.homMk (puncturedAffineLineOpen k).ι

/-- The underlying morphism of `puncturedAffineLineInclusion` is the open immersion of
`puncturedAffineLineOpen`. -/
@[simp]
theorem puncturedAffineLineInclusion_left :
    (puncturedAffineLineInclusion k).left = (puncturedAffineLineOpen k).ι :=
  rfl

/-- Negation of the standard coordinate on the affine line. -/
noncomputable def affineLineNeg : affineLine k ⟶ affineLine k :=
  Over.homMk (AffineSpace.homOfVector (affineLine k).hom
    (fun _ : PUnit.{u + 1} => -AffineSpace.coord (Spec (.of k)) PUnit.unit))

/-- The underlying morphism of `affineLineNeg` sends the coordinate to its negative. -/
@[simp]
theorem affineLineNeg_left :
    (affineLineNeg k).left = AffineSpace.homOfVector (affineLine k).hom
      (fun _ : PUnit.{u + 1} => -AffineSpace.coord (Spec (.of k)) PUnit.unit) :=
  rfl

/-- Negating the coordinate twice is the identity. -/
theorem affineLineNeg_comp_affineLineNeg :
    affineLineNeg k ≫ affineLineNeg k = 𝟙 (affineLine k) := by
  ext1
  refine AffineSpace.hom_ext ?_ ?_
  · simp
  · intro i
    rw [Over.comp_left, Over.id_left, affineLineNeg_left, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord, map_neg,
      AffineSpace.homOfVector_appTop_coord, neg_neg, Scheme.Hom.id_appTop]
    rfl

/-- Negation on the affine line is an isomorphism, being an involution. -/
instance isIso_affineLineNeg : IsIso (affineLineNeg k) :=
  ⟨affineLineNeg k, affineLineNeg_comp_affineLineNeg k,
    affineLineNeg_comp_affineLineNeg k⟩

/-- The relation scheme, the disjoint union of the affine line (carrying the diagonal) and of its
puncture (carrying the graph of negation). -/
@[stacks 02Z1 "the relation scheme Δ ⨿ Γ"]
noncomputable abbrev relationScheme : Over (Spec (.of k)) :=
  affineLine k ⨿ puncturedAffineLine k

/-- The pre-relation `j : R ⟶ U ×_k U` which is the diagonal on the first summand and the graph of
negation on the second. -/
@[stacks 02Z1 "the relation j"]
noncomputable def involutionRelation :
    Stacks.Groupoids.PreRelation (relationScheme k) (affineLine k) :=
  prod.lift
    (coprod.desc (𝟙 (affineLine k)) (puncturedAffineLineInclusion k))
    (coprod.desc (𝟙 (affineLine k))
      (puncturedAffineLineInclusion k ≫ affineLineNeg k))

/-- The target map of `involutionRelation` is the identity on the affine line and the inclusion on
the punctured affine line. -/
@[simp]
theorem involutionRelation_target :
    (involutionRelation k).target =
      coprod.desc (𝟙 (affineLine k)) (puncturedAffineLineInclusion k) := by
  simp [involutionRelation, Stacks.Groupoids.PreRelation.target]

/-- The source map of `involutionRelation` is the identity on the affine line and the inclusion
followed by negation on the punctured affine line. -/
@[simp]
theorem involutionRelation_source :
    (involutionRelation k).source =
      coprod.desc (𝟙 (affineLine k))
        (puncturedAffineLineInclusion k ≫ affineLineNeg k) := by
  simp [involutionRelation, Stacks.Groupoids.PreRelation.source]

/-- The quotient sheaf of the involution relation on a big fppf site containing `Spec k`. -/
@[stacks 02Z1 "the quotient X = U/R"]
noncomputable abbrev involutionQuotient (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    Sheaf (BigFppfOver.topology B (Spec (.of k)) hS) (Type u) :=
  Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B (Spec (.of k)) hS)
    (Over.post B.inclusion) (involutionRelation k)

/-! ### The geometry of the relation -/

/-- The affine line is an affine scheme. -/
instance isAffine_affineLine : IsAffine (affineLine k).left :=
  inferInstanceAs (IsAffine (AffineSpace PUnit.{u + 1} (Spec (.of k))))

/-- The punctured affine line is affine, being a basic open of an affine scheme. -/
instance isAffine_puncturedAffineLine : IsAffine (puncturedAffineLine k).left :=
  (isAffineOpen_top (affineLine k).left).basicOpen _

/-- The underlying morphism of `coprod.desc` in `CategoryTheory.Over S` is étale as soon as the
underlying morphisms of its two components are. -/
private theorem etale_left_coprod_desc {S : Scheme.{u}} {X Y Z : Over S} (a : X ⟶ Z) (b : Y ⟶ Z)
    (ha : Etale a.left) (hb : Etale b.left) : Etale (coprod.desc a b : X ⨿ Y ⟶ Z).left :=
  have hri : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  left_coprod_desc _ hri _ _ (property_coprod_desc _ hri
    (HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)) _ _ ha hb)

/-- The first projection `R ⟶ U` of the relation is étale: it is the identity on the diagonal
summand and the inclusion of the puncture on the other. -/
theorem etale_target : Etale (involutionRelation k).target.left := by
  rw [involutionRelation_target]
  refine etale_left_coprod_desc _ _ ?_ ?_
  · rw [Over.id_left]
    infer_instance
  · rw [puncturedAffineLineInclusion_left]
    infer_instance

/-- The second projection `R ⟶ U` of the relation is étale: it is the identity on the diagonal
summand and the inclusion of the puncture followed by the negation isomorphism on the other. -/
theorem etale_source : Etale (involutionRelation k).source.left := by
  have : IsIso (affineLineNeg k).left := (Over.forget _).map_isIso (affineLineNeg k)
  rw [involutionRelation_source]
  refine etale_left_coprod_desc _ _ ?_ ?_
  · rw [Over.id_left]
    infer_instance
  · rw [Over.comp_left, puncturedAffineLineInclusion_left]
    infer_instance

/-- The first projection `R ⟶ U` is affine. -/
theorem isAffineHom_target : IsAffineHom (involutionRelation k).target.left := by
  have hri : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [involutionRelation_target]
  refine left_coprod_desc _ hri _ _ ?_
  rw [Over.id_left, puncturedAffineLineInclusion_left]
  infer_instance

/-- The second projection `R ⟶ U` is affine. -/
theorem isAffineHom_source : IsAffineHom (involutionRelation k).source.left := by
  have hri : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [involutionRelation_source]
  refine left_coprod_desc _ hri _ _ ?_
  rw [Over.id_left, Over.comp_left, puncturedAffineLineInclusion_left]
  infer_instance

/-- The second projection `R ⟶ U` is quasi-compact, being affine. -/
theorem quasiCompact_source : QuasiCompact (involutionRelation k).source.left :=
  have := isAffineHom_source k
  inferInstance

/-- The affine line is quasi-separated over `Spec k`, being affine. -/
theorem quasiSeparated_affineLine : QuasiSeparated (affineLine k).hom :=
  inferInstanceAs (QuasiSeparated ((AffineSpace PUnit.{u + 1} (Spec (.of k))) ↘ Spec (.of k)))

end AffineLineInvolution

end AlgebraicGeometry

end
