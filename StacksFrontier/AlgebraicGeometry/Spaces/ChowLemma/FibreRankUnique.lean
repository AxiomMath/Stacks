module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Degree
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedChartTopStratum
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalFibreDegree

/-!
# The fibre degree of a chart is unique, and drops strictly off the minimal-degree locus

The induction of Stacks 089J passes from an algebraic space `X` with a chart of minimal fibre
degree `d` to the complement of the open locus where that degree is attained, and needs to know
that the fibre degree of the chart *there* is strictly smaller than `d`. The degree
stratification of Stacks 07S8 gives that for a degree already known to be at most `d`, because
the characterisation of the strata it provides only runs up to `d`.

This file removes that restriction. The missing ingredient is uniqueness of the rank of a finite
locally free morphism over a base with a point, which is
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.rank_eq_of_point`: a point of the complement is
presented by the spectrum of a field, the stratification names the degree `s < d` of the chart
above that field-valued point, the given degree `r` restricts to the same morphism of schemes,
and so `r = s`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_presheaf`: the relative form of being
  finite locally free of rank `r`, read off at one representable base change.
* `AlgebraicGeometry.Space.eq_of_presheaf_isFiniteLocallyFreeOfRank`: **uniqueness of the
  relative fibre degree.** A morphism of presheaves which is relatively finite locally free of
  rank `r` and of rank `s`, and which admits a representable base change whose base scheme has
  a point, has `r = s`.
* `AlgebraicGeometry.Space.lt_of_presheaf_isFiniteLocallyFreeOfRank_of_range_subset`: the
  strict drop of the degree off the top stratum, with **no** hypothesis bounding the degree.
* `AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'`: the
  minimal-degree locus of a separated étale chart together with the strict drop on its
  complement, again with no bound hypothesis. This is
  `AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt_of_isEtale`
  with its residual hypothesis `r ≤ d` discharged.

## What is and is not proved

Stacks 089J is **not** proved here and no declaration in this file carries a Stacks attribute:
the stratification is Stacks 07S8, carried by
`AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank`, uniqueness of the rank
of a locally free module is Stacks 01C9, carried by
`LocallyFreeRank.Trivialization.rank_eq_of_mem`, and the choice of the least degree bound is an
unlabelled step of the proof of Stacks 089J taken in
`StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalFibreDegree`.

What is **not** proved is the induction of Stacks 089J itself. The reduced induced closed
subspace on the complement of the minimal-degree locus is not formed here, nor are its side
conditions — separatedness over the base, affineness of its chart base change, reasonableness —
discharged; and the properness and surjectivity of the cover over the minimal-degree locus are
elsewhere and incomplete. This file closes exactly one residue: the degree hypothesis that
`AlgebraicGeometry.Space.lt_of_isFiniteLocallyFreeOfRank_of_range_subset_strata` left to its
consumer.

## References

* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relative fibre degree, read off at one representable base change.** If `pr₂` is
relatively finite locally free of rank `r` in the sense of
`CategoryTheory.MorphismProperty.presheaf`, then every base change of it along a morphism from
a representable presheaf is, as a morphism of schemes, finite locally free of rank `r`.

This is the second component of `CategoryTheory.MorphismProperty.relative` spelled out. -/
theorem isFiniteLocallyFreeOfRank_of_presheaf
    {Pp T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pr₂ : Pp ⟶ T} {r : ℕ}
    (h : (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf pr₂)
    {a b : BigFppfOver B S hS} (γ : yoneda.obj a ⟶ T) (fst : yoneda.obj b ⟶ Pp) (snd : b ⟶ a)
    (hsq : IsPullback fst (yoneda.map snd) pr₂ γ) :
    IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map snd) r :=
  h.2 γ fst snd hsq

/-- **Uniqueness of the relative fibre degree.** A morphism of presheaves on the big fppf site
over `S` which is relatively finite locally free of rank `r` and also of rank `s` has `r = s`,
provided some representable presheaf maps to its target in such a way that the underlying
scheme has at least one point.

Both ranks are read off at the *same* base change, which exists because a relatively finite
locally free morphism is in particular relatively representable; the statement is then
uniqueness of the rank of a finite locally free morphism of schemes over a base with a point,
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.rank_eq_of_point`. -/
theorem eq_of_presheaf_isFiniteLocallyFreeOfRank
    {Pp T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pr₂ : Pp ⟶ T} {r s : ℕ}
    (hr : (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf pr₂)
    (hs : (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} s)
      (BigFppfOver.toScheme B S hS)).presheaf pr₂)
    {a : BigFppfOver B S hS} (γ : yoneda.obj a ⟶ T)
    (x : (BigFppfOver.toScheme B S hS).obj a) :
    r = s := by
  obtain ⟨b, snd, fst, hsq⟩ := hr.1 γ
  exact IsFiniteLocallyFreeOfRank.rank_eq_of_point _ x
    (isFiniteLocallyFreeOfRank_of_presheaf B S hS hr γ fst snd hsq)
    (isFiniteLocallyFreeOfRank_of_presheaf B S hS hs γ fst snd hsq)

/-- **The fibre degree of a chart drops strictly on the top closed stratum**, with no
hypothesis bounding that degree.

The data is the degree stratification of Stacks 07S8 in the form
`AlgebraicGeometry.Space.exists_minimal_closedChain_isFiniteLocallyFreeOfRank` produces it: a
chain of sets `Z` starting at `∅` whose consecutive difference `Z (r + 1) ∖ Z r` is, for
`r ≤ d`, exactly the locus over which the chart base change is finite locally free of degree
`r`. A morphism into `X` with at least one point whose image lies in `Z d` and whose chart base
change is finite locally free of degree `r` has `r < d`.

A point of the source is represented by a field-valued point `Spec K ⟶ T`, whose image in `X`
is a single point `x` of `Z d` by
`AlgebraicGeometry.Space.range_pointsMap_yonedaEquiv_symm`. Since `Z 0 = ∅`, the least `s` with
`x ∈ Z (s + 1)` satisfies `s < d` and `x ∉ Z s`, so the characterisation applies at `s` to the
base change of the chart along `Spec K ⟶ T ⟶ X`. That base change is also the base change of
`pr₂` along `Spec K ⟶ T`, so it carries both degrees, and `Spec K` has a point; hence `r = s`
by `AlgebraicGeometry.Space.eq_of_presheaf_isFiniteLocallyFreeOfRank`.

This is the statement
`AlgebraicGeometry.Space.lt_of_isFiniteLocallyFreeOfRank_of_range_subset_strata` leaves to its
consumer, with the residual hypothesis `r ≤ d` discharged. -/
theorem lt_of_presheaf_isFiniteLocallyFreeOfRank_of_range_subset
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X)
    (d : ℕ) (Z : ℕ → Set (points B S hS X)) (hZ0 : Z 0 = ∅)
    (hZchar : ∀ r : ℕ, r ≤ d → ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X),
      IsAlgebraicSpace B S hS T →
      ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
        IsPullback pr₁ pr₂ g hm →
        ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
            (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
          Set.range (pointsMap B S hS T hm) ⊆ Z (r + 1) \ Z r))
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X)
    (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T)
    (hsq : IsPullback pr₁ pr₂ g hm) (t : points B S hS T)
    (hTsub : Set.range (pointsMap B S hS T hm) ⊆ Z d) (r : ℕ)
    (hflf : (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf pr₂) :
    r < d := by
  classical
  -- a field-valued representative of the given point, and the morphism it presents
  obtain ⟨p, -⟩ := Quot.exists_rep t
  set γ : yoneda.obj (FieldValuedPoint.siteObject B S hS T p) ⟶ T := yonedaEquiv.symm p.value
    with hγ
  set x : points B S hS X := pointsMap B S hS T hm (p.class B S hS T) with hxdef
  have hrange : Set.range (pointsMap B S hS
      (yoneda.obj (FieldValuedPoint.siteObject B S hS T p)) (γ ≫ hm)) = {x} := by
    rw [pointsMap_comp, Set.range_comp, hγ, range_pointsMap_yonedaEquiv_symm,
      Set.image_singleton]
  have hx : x ∈ Z d := hTsub ⟨p.class B S hS T, rfl⟩
  -- the stratum containing that point
  have hx0 : x ∉ Z 0 := by simp [hZ0]
  have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hx0 hx)
  have hex : ∃ m : ℕ, x ∈ Z (m + 1) := ⟨d - 1, by rwa [Nat.sub_add_cancel hdpos]⟩
  set s : ℕ := Nat.find hex with hsdef
  have hsmem : x ∈ Z (s + 1) := Nat.find_spec hex
  have hslt : s < d := lt_of_le_of_lt (Nat.find_le (p := fun m ↦ x ∈ Z (m + 1))
    (by rwa [Nat.sub_add_cancel hdpos])) (by omega)
  have hsnot : x ∉ Z s := by
    by_cases h0 : s = 0
    · rwa [h0]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [hk]
      exact Nat.find_min hex (by omega)
  -- the base change of the chart along the field-valued point, taken through `pr₂`
  obtain ⟨b, snd, fst, hsq2⟩ := hflf.1 γ
  have hpaste : IsPullback (fst ≫ pr₁) (yoneda.map snd) g (γ ≫ hm) :=
    hsq2.paste_horiz hsq
  have hsrank : (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} s)
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map snd) :=
    (hZchar s hslt.le _ (γ ≫ hm)
      (isAlgebraicSpace_yoneda B S hS (FieldValuedPoint.siteObject B S hS T p)) _
      (fst ≫ pr₁) (yoneda.map snd) hpaste).2 (by
        rw [hrange]
        exact Set.singleton_subset_iff.2 ⟨hsmem, hsnot⟩)
  -- both degrees are carried by one morphism of schemes over the spectrum of a field
  have hsq3 : IsPullback (𝟙 (yoneda.obj b)) (yoneda.map snd) (yoneda.map snd)
      (𝟙 (yoneda.obj (FieldValuedPoint.siteObject B S hS T p))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hrk : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map snd) r :=
    isFiniteLocallyFreeOfRank_of_presheaf B S hS hflf γ fst snd hsq2
  have hsk : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map snd) s :=
    isFiniteLocallyFreeOfRank_of_presheaf B S hS hsrank (𝟙 _) (𝟙 _) snd hsq3
  have : r = s :=
    IsFiniteLocallyFreeOfRank.rank_eq_of_point _
      (Classical.arbitrary (Spec (CommRingCat.of p.carrier))) hrk hsk
  omega

/-- **The minimal-degree locus of a separated étale chart, with the strict drop of the degree
on its complement and no hypothesis bounding that degree.**

This is
`AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt_of_isEtale` with
its residual hypothesis `r ≤ d` removed: besides the nonempty open set `U` of points over which
the chart base change is finite locally free of degree exactly `d`, a morphism into `X` with at
least one point whose image misses `U` has chart base change of degree strictly less than `d`,
whatever that degree is.

Both clauses come from the chain
`AlgebraicGeometry.Space.exists_minimal_closedChain_isFiniteLocallyFreeOfRank`; the second is
`AlgebraicGeometry.Space.lt_of_presheaf_isFiniteLocallyFreeOfRank_of_range_subset`. -/
theorem exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
    (g : yoneda.obj W ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hR : IsReasonableSpace B S hS X)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hgEt : IsEtale B S hS g) (hsep : IsSeparated B S hS g)
    (hne : Nonempty (points B S hS X)) :
    ∃ (d : ℕ) (U : Set (points B S hS X)), IsOpen U ∧ U.Nonempty ∧
      (∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X), IsAlgebraicSpace B S hS T →
        ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ g hm →
          ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} d)
              (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
            Set.range (pointsMap B S hS T hm) ⊆ U)) ∧
      ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X)
        (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ g hm → points B S hS T →
            Set.range (pointsMap B S hS T hm) ⊆ Uᶜ →
              ∀ r : ℕ,
                (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
                  (BigFppfOver.toScheme B S hS)).presheaf pr₂ → r < d := by
  obtain ⟨d, Z, hZ0, hZcl, -, hZtop, hZd, hZchar⟩ :=
    exists_minimal_closedChain_isFiniteLocallyFreeOfRank B S hS X W g hX
      (isFlat_of_isEtale B S hS hgEt) (isLocallyOfFinitePresentation_of_isEtale B S hS hgEt)
      hsep (isLocallyQuasiFinite_of_isEtale B S hS hX hgEt)
      (hR W hW g ((isEtale_iff_presheaf_of_yoneda B S hS g).1 hgEt)) hne
  refine ⟨d, (Z d)ᶜ, (hZcl d).isOpen_compl, Set.nonempty_compl.2 hZd, ?_, ?_⟩
  · intro T hm hT Pp pr₁ pr₂ hsq
    have h := hZchar d le_rfl T hm hT Pp pr₁ pr₂ hsq
    rw [hZtop] at h
    rwa [Set.compl_eq_univ_sdiff]
  · intro T hm Pp pr₁ pr₂ hsq t hTsub r hflf
    exact lt_of_presheaf_isFiniteLocallyFreeOfRank_of_range_subset B S hS W g d Z hZ0 hZchar
      T hm Pp pr₁ pr₂ hsq t (by rwa [compl_compl] at hTsub) r hflf

end AlgebraicGeometry.Space

end
