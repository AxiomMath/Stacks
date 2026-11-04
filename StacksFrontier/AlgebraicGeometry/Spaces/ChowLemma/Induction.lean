module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ClosedStratumChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductChowCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.TopStratumCover
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent

/-!
# Chow's lemma for algebraic spaces

This file completes [Stacks, Tag 089J]: an algebraic space `X` over `Spec A` whose structure
morphism is separated and of finite type is the target of a proper surjective morphism `X' ⟶ X`
whose source is a *scheme*, H-quasi-projective over `Spec A`.

Everything but the recursion is in place elsewhere in this directory:
`AlgebraicGeometry.Space.exists_chowCover_minimalDegreeOpen` performs the construction once and
produces a proper morphism from an H-quasi-projective scheme whose image contains the open `U` on
which the fibre degree of a chosen affine étale chart is largest, together with the strict drop of
that degree off `U`. What is added here is the strong induction on that degree.

The step is the source's: `U` is covered by the morphism just produced; the complement `|X| ∖ U`,
taken with its reduced induced structure `T`, is again separated and of finite type over `Spec A`
by permanence along the closed immersion `T ⟶ X`, and the chart it inherits is affine, surjective
and étale with every fibre of degree strictly less than `d`, so the induction hypothesis covers
`T` properly and surjectively by an H-quasi-projective scheme; the composite with `T ⟶ X` is
proper because a closed immersion is; and the two morphisms together cover `X`, so
`AlgebraicGeometry.Space.hasChowSchemeCover_of_isProper_pair` assembles them. The recursion
bottoms out because an algebraic space with no points has its chart for a Chow cover: the chart
is then étale, surjective and universally injective, hence an isomorphism by Stacks 05W5.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.hasChowSchemeCover_of_isEmpty_points`: an algebraic space with no
  points has a Chow scheme cover, namely its own affine étale chart.
* `AlgebraicGeometry.Space.hasChowSchemeCover_of_chart_fibre_le`: **the induction.** An algebraic
  space separated and of finite type over `Spec A` carrying an affine surjective étale chart all
  of whose field-valued fibres have degree at most `d` has a Chow scheme cover.
* `AlgebraicGeometry.Space.hasChowSchemeCover_of_isSeparated_isFiniteType`: **[Stacks, Tag
  089J].** An algebraic space over `Spec A` whose structure morphism is separated and of finite
  type has a Chow scheme cover.
* `AlgebraicGeometry.Space.chowLemmaForSpaces`:
  `AlgebraicGeometry.Space.ChowLemmaForSpaces`, the same statement as recorded in this
  directory's `Basic` file, discharged.

## Implementation notes

The induction is on a bound for the fibre degrees of a chart, not on the degree of the chart over
the top stratum, because the complement stratum carries a *different* chart — the base change of
the given one — and it is for that chart that the degree drops. The bound is in the shape of the
third clause of `AlgebraicGeometry.Space.exists_minimalDegreeOpen_and_fibre_le_degree`, which is
also what starts the induction off: applied to the chart of `X` it produces a bound with no
hypothesis beyond separatedness.

That the degree over the top stratum is at most the given bound — needed for the recursive call
to be at a strictly smaller index — is read off a point of that stratum: the two degrees are
degrees of one and the same morphism of schemes, so they agree by
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.rank_eq_of_point`.

The case in which the complement of the top stratum is empty is treated separately rather than by
recursion into the empty algebraic space, because in that case the morphism already produced is
surjective on the nose.

## What is and is not proved

[Stacks, Tag 089J] **is** proved here, unconditionally:
`AlgebraicGeometry.Space.hasChowSchemeCover_of_isSeparated_isFiniteType` carries the attribute,
and neither it nor anything it rests on takes properness, surjectivity, H-quasi-projectivity or
any form of the conclusion as a hypothesis. The source `X'` of the cover is produced as an object
of the chosen big fppf site, which is the convention of this directory and no loss, the `X'` of
the tag being cut out of a finite product of compactifications of an étale chart of `X`.

The proof is the source's, through: Stacks 03H6 for the affine surjective étale chart, Stacks
03JX for reasonableness of a separated algebraic space, Stacks 07S8 for the degree
stratification, Stacks 01WA for the projective compactification of the chart, Stacks 03IQ for
the reduced induced structure on the complement, Stacks 04XZ and 04XY for properness of the
composite with the closed immersion, and the refined valuative criterion of Stacks 089G for
properness of the cover itself.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The base of the induction -/

/-- **An algebraic space with no points has a Chow scheme cover: its own affine étale chart.**

The chart has no points either, so it is universally injective — every base change of it has a
point set mapping into the empty point set of the chart — and an étale, universally injective,
surjective morphism of algebraic spaces is an isomorphism by Stacks 05W5. An isomorphism is
proper, and the chart, being an affine scheme with empty underlying space, is H-quasi-projective
over the base: it is affine and its structure morphism is locally of finite type because a
morphism out of an empty scheme is an open immersion. -/
theorem hasChowSchemeCover_of_isEmpty_points
    (B : BigFppfSite.{u}) (A : CommRingCat.{u}) (hA : B.Contains (Spec A))
    (X : AlgebraicSpaces B (Spec A) hA)
    (Wch : BigFppfOver B (Spec A) hA) (c : yoneda.obj Wch ⟶ X.obj)
    (hc : IsEtale B (Spec A) hA c) (hcs : IsSurjective B (Spec A) hA c)
    (hempty : IsEmpty (points B (Spec A) hA X.obj)) :
    HasChowSchemeCover B (Spec A) hA X.obj := by
  have hWempty : IsEmpty (points B (Spec A) hA (yoneda.obj Wch)) :=
    ⟨fun w ↦ hempty.elim (pointsMap B (Spec A) hA (yoneda.obj Wch) c w)⟩
  have hWsch : IsEmpty (B.inclusion.obj Wch.left) :=
    ⟨fun z ↦ hWempty.elim ((pointsEquivScheme B (Spec A) hA Wch).symm z)⟩
  have hui : UniversallyInjective B (Spec A) hA c := by
    intro Y' _ g a _ _
    exact hWempty.elim
      (pointsMap B (Spec A) hA (pullback g c) (pullback.snd g c) a)
  have hiso : IsIso c :=
    isIso_of_isEtale_of_universallyInjective_of_isSurjective B (Spec A) hA
      (isAlgebraicSpace_yoneda B (Spec A) hA Wch) X.property c hc hui hcs
  have _ := hiso
  have _ := hWsch
  have _ : IsAffine (B.inclusion.obj Wch.left) := inferInstance
  have _ : LocallyOfFiniteType (B.inclusion.map Wch.hom) := inferInstance
  exact ⟨Wch, c, isProper_of_isIso B (Spec A) hA c, hcs,
    isHQuasiProjective_of_isAffine_toSpec (B.inclusion.map Wch.hom)⟩

/-! ### The induction on the fibre degree -/

/-- **The induction of [Stacks, Tag 089J] on the fibre degree of a chart.**

Let `X` be an algebraic space over `Spec A`, separated and of finite type over the base, and let
`c : h_W ⟶ X` be an affine surjective étale chart every field-valued fibre of which is finite
locally free of degree at most `d`. Then `X` has a Chow scheme cover.

The induction is strong induction on `d`. If `X` has no points the chart itself is a cover, by
`AlgebraicGeometry.Space.hasChowSchemeCover_of_isEmpty_points`. Otherwise
`AlgebraicGeometry.Space.exists_chowCover_minimalDegreeOpen` produces the degree `d'` of the
chart over its top stratum `U`, a proper morphism from a scheme H-quasi-projective over the base
whose image contains `U`, and the strict drop of the degree off `U`; and `d' ≤ d`, the two being
degrees of one morphism of schemes at a point of `U`.

If `U` is the whole point set, that morphism is already surjective and we are done. Otherwise its
complement carries the reduced induced structure of Stacks 03IQ, which is a closed subspace,
hence an algebraic space separated and of finite type over the base; the chart it inherits is
affine, surjective and étale with fibre degrees strictly below `d'`, hence at most `d' - 1 < d`,
so the induction hypothesis applies to it. The composite of the resulting cover with the closed
immersion is proper by Stacks 04XZ and 04XY, and the two covers together meet every point of `X`,
so `AlgebraicGeometry.Space.hasChowSchemeCover_of_isProper_pair` assembles them. -/
theorem hasChowSchemeCover_of_chart_fibre_le
    (B : BigFppfSite.{u}) (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (d : ℕ) :
    ∀ X : AlgebraicSpaces B (Spec A) hA,
      IsSeparated B (Spec A) hA ((isTerminal_yoneda_obj_base B (Spec A) hA).from X.obj) →
      IsFiniteType B (Spec A) hA ((isTerminal_yoneda_obj_base B (Spec A) hA).from X.obj) →
      ∀ (Wch : BigFppfOver B (Spec A) hA) (c : yoneda.obj Wch ⟶ X.obj),
        IsEtale B (Spec A) hA c → IsSurjective B (Spec A) hA c →
        IsAffine ((BigFppfOver.toScheme B (Spec A) hA).obj Wch) →
        (∀ (K : Type u) (_ : Field K) (T : BigFppfOver B (Spec A) hA)
          (_ : (BigFppfOver.toScheme B (Spec A) hA).obj T ≅ Spec (CommRingCat.of K))
          (ξ : yoneda.obj T ⟶ X.obj) (Vf : BigFppfOver B (Spec A) hA) (q : Vf ⟶ T)
          (i : yoneda.obj Vf ⟶ yoneda.obj Wch),
          IsPullback i (yoneda.map q) c ξ →
            ∃ r : ℕ, r ≤ d ∧
              IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B (Spec A) hA).map q) r) →
        HasChowSchemeCover B (Spec A) hA X.obj := by
  classical
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro X hXsep hft Wch c hc hcs hW hbd
  rcases isEmpty_or_nonempty (points B (Spec A) hA X.obj) with hemp | hne
  · exact hasChowSchemeCover_of_isEmpty_points B A hA X Wch c hc hcs hemp
  obtain ⟨d', U, hUopen, hUne, hd'pos, hU1, ⟨X₁, p₁, hp₁prop, hp₁qp, hp₁cov⟩, hU2, hU3⟩ :=
    exists_chowCover_minimalDegreeOpen B A hA X hXsep hft Wch c hc hcs hW hne
  -- the degree over the top stratum is at most the given bound
  have hd'le : d' ≤ d := by
    obtain ⟨x, hxU⟩ := hUne
    obtain ⟨p, hp⟩ := Quot.exists_rep x
    set ξ : yoneda.obj p.siteObject ⟶ X.obj := yonedaEquiv.symm p.value with hξ
    have hxval : ∀ z, pointsMap B (Spec A) hA (yoneda.obj p.siteObject) ξ z = x := fun z ↦
      (FieldValuedPoint.pointsMap_eq_class B (Spec A) hA p z).trans hp
    have hcp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec A) hA)).presheaf c :=
      (isEtale_iff_presheaf_of_yoneda B (Spec A) hA c).1 hc
    have hsq : IsPullback (yoneda.map (hcp.rep.fst' ξ)) (yoneda.map (hcp.rep.snd ξ)) c ξ :=
      hcp.rep.isPullback' ξ
    have hflf := (hU1 (yoneda.obj p.siteObject) ξ
      (isAlgebraicSpace_yoneda B (Spec A) hA p.siteObject)
      (yoneda.obj (hcp.rep.pullback ξ)) (yoneda.map (hcp.rep.fst' ξ))
      (yoneda.map (hcp.rep.snd ξ)) hsq).2 (by
        rintro y ⟨z, rfl⟩
        rw [hxval z]
        exact hxU)
    have hid : IsPullback (𝟙 (yoneda.obj (hcp.rep.pullback ξ)))
        (yoneda.map (hcp.rep.snd ξ)) (yoneda.map (hcp.rep.snd ξ))
        (𝟙 (yoneda.obj p.siteObject)) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    have hrank' : IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B (Spec A) hA).map (hcp.rep.snd ξ)) d' :=
      isFiniteLocallyFreeOfRank_of_presheaf B (Spec A) hA hflf (𝟙 _) (𝟙 _) (hcp.rep.snd ξ) hid
    obtain ⟨r, hrle, hrank⟩ := hbd p.carrier p.field p.siteObject (Iso.refl _) ξ
      (hcp.rep.pullback ξ) (hcp.rep.snd ξ) (yoneda.map (hcp.rep.fst' ξ)) hsq
    have hdr : d' = r := IsFiniteLocallyFreeOfRank.rank_eq_of_point _
      (Classical.arbitrary (Spec (CommRingCat.of p.carrier))) hrank' hrank
    omega
  rcases eq_or_ne Uᶜ (∅ : Set (points B (Spec A) hA X.obj)) with hUc | hUc
  · -- the top stratum is everything, so the morphism already produced is surjective
    refine ⟨X₁, p₁, hp₁prop, fun x ↦ hp₁cov ?_, hp₁qp⟩
    by_contra hx
    exact (Set.eq_empty_iff_forall_notMem.1 hUc x) hx
  · -- the complement of the top stratum, with its reduced induced structure
    have hUcl : _root_.IsClosed (Uᶜ : Set (points B (Spec A) hA X.obj)) := hUopen.isClosed_compl
    set G := reducedClosedSubspace B (Spec A) hA X.obj X.property Uᶜ hUcl
    have hGalg : IsAlgebraicSpace B (Spec A) hA G.toFunctor :=
      isAlgebraicSpace_reducedClosedSubspace B (Spec A) hA X.obj X.property Uᶜ hUcl
    have hGι : IsClosedImmersion B (Spec A) hA G.ι :=
      isClosedImmersion_ι_reducedClosedSubspace B (Spec A) hA X.property Uᶜ hUcl
    have hGrange : Set.range (pointsMap B (Spec A) hA G.toFunctor G.ι) = Uᶜ :=
      range_pointsMap_ι_reducedClosedSubspace B (Spec A) hA X.obj X.property Uᶜ hUcl
    have htri : (isTerminal_yoneda_obj_base B (Spec A) hA).from G.toFunctor =
        G.ι ≫ (isTerminal_yoneda_obj_base B (Spec A) hA).from X.obj :=
      (isTerminal_yoneda_obj_base B (Spec A) hA).hom_ext _ _
    have hGsep : IsSeparated B (Spec A) hA
        ((isTerminal_yoneda_obj_base B (Spec A) hA).from G.toFunctor) := by
      rw [htri]
      exact isSeparated_comp B (Spec A) hA _ _
        (isSeparated_of_isClosedImmersion B (Spec A) hA _ hGι) hXsep
    have hGft : IsFiniteType B (Spec A) hA
        ((isTerminal_yoneda_obj_base B (Spec A) hA).from G.toFunctor) := by
      rw [htri]
      exact isFiniteType_comp B (Spec A) hA hGalg X.property
        (isAlgebraicSpace_yoneda B (Spec A) hA (Over.mk (𝟙 (B.obj hA)))) _ _
        (isFiniteType_of_isClosedImmersion B (Spec A) hA _ hGι) hft
    obtain ⟨WT, cT, pW, hWT, hcTe, hcTs, hsqT⟩ :=
      exists_chart_of_isClosedSubspace B (Spec A) hA X.property _ hGι Wch c hc hcs hW
    have hbdT := exists_lt_of_chart_of_isClosedSubspace B (Spec A) hA G Wch c WT cT pW hsqT U d'
      hU2 hU3 hGrange.le
    obtain ⟨X₂, p₂, hp₂prop, hp₂surj, hp₂qp⟩ :=
      ih (d' - 1) (by omega) ⟨G.toFunctor, hGalg⟩ hGsep hGft WT cT hcTe hcTs hWT
        (fun K hK T eT ξ Vf q i hsqi ↦ by
          obtain ⟨r, hlt, hrank⟩ := hbdT K hK T eT ξ Vf q i hsqi
          exact ⟨r, by omega, hrank⟩)
    refine hasChowSchemeCover_of_isProper_pair B (Spec A) hA X.property X₁ X₂ p₁ (p₂ ≫ G.ι)
      hp₁prop ?_ hp₁qp hp₂qp ?_
    · exact isProper_comp B (Spec A) hA (isAlgebraicSpace_yoneda B (Spec A) hA X₂) hGalg
        X.property p₂ _ hp₂prop
        (isProper_of_isClosedImmersion B (Spec A) hA hGalg X.property _ hGι)
    · intro x
      by_cases hxU : x ∈ U
      · exact Or.inl (hp₁cov hxU)
      · obtain ⟨y, hy⟩ : x ∈ Set.range (pointsMap B (Spec A) hA G.toFunctor G.ι) := by
          rw [hGrange]; exact hxU
        obtain ⟨z, hz⟩ := hp₂surj y
        refine Or.inr ⟨z, ?_⟩
        rw [pointsMap_comp B (Spec A) hA (yoneda.obj X₂) p₂ _, Function.comp_apply, hz, hy]

/-! ### Chow's lemma -/

/-- **Chow's lemma for algebraic spaces, [Stacks, Tag 089J].**

Let `A` be a ring whose spectrum lies in the chosen big fppf site, and let `X` be an algebraic
space over `Spec A` whose structure morphism is separated and of finite type. Then there is an
object `X'` of the site — a scheme over `Spec A` — and a proper surjective morphism from the
presheaf it represents to `X`, such that the structure morphism of `X'` to `Spec A` is
H-quasi-projective.

The morphism `f` quantified over is the structure morphism of `X` and nothing else: its target
is the presheaf represented by the base, which is terminal by
`AlgebraicGeometry.Space.isTerminal_yoneda_obj_base`.

The proof is Stacks 089J's. An affine surjective étale chart exists by Stacks 03H6; a separated
algebraic space over an affine base is reasonable by Stacks 03JX, so the fibre degrees of that
chart are bounded, by the degree stratification of Stacks 07S8; and
`AlgebraicGeometry.Space.hasChowSchemeCover_of_chart_fibre_le` performs the induction on that
bound. -/
@[stacks 089J]
theorem hasChowSchemeCover_of_isSeparated_isFiniteType
    (B : BigFppfSite.{u}) (A : CommRingCat.{u}) (hA : B.Contains (Spec A))
    (X : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec A) hA X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hsep : IsSeparated B (Spec A) hA f) (hft : IsFiniteType B (Spec A) hA f) :
    HasChowSchemeCover B (Spec A) hA X := by
  classical
  have hf : f = (isTerminal_yoneda_obj_base B (Spec A) hA).from X :=
    (isTerminal_yoneda_obj_base B (Spec A) hA).hom_ext _ _
  rw [hf] at hsep hft
  obtain ⟨Wch, c, hW, hcsurj, hc⟩ :=
    exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact B (Spec A) hA hX
      ((isTerminal_yoneda_obj_base B (Spec A) hA).from X) hft.2
  have hcs : IsSurjective B (Spec A) hA c :=
    isSurjective_of_presheafSurjective B (Spec A) hA c hcsurj
  rcases isEmpty_or_nonempty (points B (Spec A) hA X) with hemp | hne
  · exact hasChowSchemeCover_of_isEmpty_points B A hA ⟨X, hX⟩ Wch c hc hcs hemp
  have hWsep : Scheme.IsSeparated ((BigFppfOver.toScheme B (Spec A) hA).obj Wch) := by
    have := hW
    infer_instance
  have hsepc : IsSeparated B (Spec A) hA c :=
    isSeparated_of_isEtale_of_scheme_isSeparated B (Spec A) hA X hX Wch hWsep c hc
  have hR : IsReasonableSpace B (Spec A) hA X :=
    isReasonableSpace_of_isSeparated_toBase B (Spec A) hA inferInstance X hX hsep
  obtain ⟨d, -, -, -, -, -, hU3⟩ :=
    exists_minimalDegreeOpen_and_fibre_le_degree B (Spec A) hA X Wch c hX hR hW hc hsepc hne
  exact hasChowSchemeCover_of_chart_fibre_le B A hA d ⟨X, hX⟩ hsep hft Wch c hc hcs hW hU3

/-- **`AlgebraicGeometry.Space.ChowLemmaForSpaces`, discharged.** This is the proposition
recorded in `StacksFrontier/AlgebraicGeometry/Spaces/ChowLemma/Basic.lean` so that consumers could
take [Stacks, Tag 089J] as an explicit hypothesis; it is
`AlgebraicGeometry.Space.hasChowSchemeCover_of_isSeparated_isFiniteType` with its arguments
reassembled, and no consumer needs to assume it any longer. -/
theorem chowLemmaForSpaces (B : BigFppfSite.{u}) : ChowLemmaForSpaces B :=
  fun A hA X hX f hsep hft ↦
    hasChowSchemeCover_of_isSeparated_isFiniteType B A hA X hX f hsep hft

end AlgebraicGeometry.Space

end
