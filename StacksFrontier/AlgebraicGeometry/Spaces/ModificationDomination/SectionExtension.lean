module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.QcqsBase
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGlueing

/-!
# Extending a section of a proper morphism over an open by an admissible blowup

Let `S` be a scheme, let `Y` be a quasi-compact and quasi-separated algebraic space over `S`, let
`U ⊆ W ⊆ Y` be quasi-compact open subspaces, let `f : X ⟶ W` be proper and let `s : U ⟶ X` satisfy
`f ∘ s = id_U`. Then there are a `U`-admissible blowup `b : Y' ⟶ Y` and a morphism
`s' : b⁻¹(W) ⟶ X` extending `s` with `f ∘ s' = b|_{b⁻¹(W)}`. This is Stacks 0CPI.

## The proof

* Over a quasi-compact quasi-separated algebraic space `W` (the case `W = Y`), `X` is replaced by
  the scheme-theoretic image `X̃` of `s`: it is proper over `W` and `X̃ ⟶ W` is an isomorphism over
  `U` (Stacks 0CP3,
  `AlgebraicGeometry.Space.isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section`).
  Stacks 087G (`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_dominating_of_isProper`) gives a
  `U`-admissible blowup `W' ⟶ W` dominating `X̃`, and the domination extends `s` because two
  morphisms to `X̃` over `W` agree over `U`. This is
  `AlgebraicGeometry.Space.dominatesSections_of_isQuasiCompactSpace`.
* In general `W` is a quasi-compact quasi-separated algebraic space (an open subspace of the
  quasi-separated `Y`), so the first step applies to `W`; Stacks 086D
  (`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isPullback'`) extends the `U`-admissible
  blowup `W' ⟶ W` to a `U`-admissible blowup `b : Y' ⟶ Y` whose restriction to `W` is `W'`, and
  `s'` is the morphism `b⁻¹(W) ≅ W' ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.dominatesSections_of_isQuasiCompactSpace`: Stacks 0CPI for `W = Y`.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_extending_section_of_isProper`:
  **Stacks 0CPI**.

## References

* [Stacks Project, Tag 0CPI](https://stacks.math.columbia.edu/tag/0CPI)
* [Stacks Project, Tag 0CP3](https://stacks.math.columbia.edu/tag/0CP3)
* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
* [Stacks Project, Tag 086D](https://stacks.math.columbia.edu/tag/086D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A quasi-compact quasi-separated algebraic space dominates sections**: Stacks 0CPI for
`W = Y`. Following the source, `X` is replaced by the scheme-theoretic image of the section, which
is an isomorphism over `U` by Stacks 0CP3, and Stacks 087G is applied to it. -/
theorem dominatesSections_of_isQuasiCompactSpace (Y : AlgebraicSpaces B S hS)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1) :
    DominatesSections Y := by
  intro U hUqc X f hf s hs
  have hUι : IsQuasiCompact B S hS U.1.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal Y.2 hYqs hUqc U.1.ι
  have hXtcl : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS s) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS s X.2
  have hiso : IsIso (pullback.snd ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f.hom) U.1.ι) :=
    isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section B S hS X.2 Y.2 f.hom hf.1
      U.1 U.2 hUι s hs
  have hft : IsProper B S hS ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f.hom) :=
    isProper_comp B S hS hXtcl.1 X.2 Y.2 _ _ (isProper_of_isClosedImmersion B S hS hXtcl.1 X.2 _
      hXtcl.2) hf
  let XT : AlgebraicSpaces B S hS := ⟨(schemeTheoreticImageSubfunctor B S hS s).toFunctor, hXtcl.1⟩
  let fT : XT ⟶ Y := ObjectProperty.homMk ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f.hom)
  obtain ⟨Y', b, hb, g, hg⟩ :=
    exists_isAdmissibleBlowup_dominating_of_isProper fT hYqc hYqs U hUqc hft hiso
  have hg' : g.hom ≫ (schemeTheoreticImageSubfunctor B S hS s).ι ≫ f.hom = b.hom :=
    congrArg (fun m => m.hom) hg
  refine ⟨Y', b, hb, ObjectProperty.homMk (g.hom ≫ (schemeTheoreticImageSubfunctor B S hS s).ι),
    ?_, ?_⟩
  · refine ObjectProperty.hom_ext _ ?_
    show (g.hom ≫ (schemeTheoreticImageSubfunctor B S hS s).ι) ≫ f.hom = b.hom
    rw [Category.assoc]
    exact hg'
  · let st : U.1.toFunctor ⟶ (schemeTheoreticImageSubfunctor B S hS s).toFunctor :=
      Subfunctor.lift s (range_le_schemeTheoreticImageSubfunctor B S hS s)
    have hst : st ≫ (schemeTheoreticImageSubfunctor B S hS s).ι = s := Subfunctor.lift_ι _ _
    have h := eq_of_comp_eq_of_isIso_pullback_snd
      ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f.hom) U.1
      (p := (U.1.preimage b.hom).ι ≫ g.hom) (q := U.1.fromPreimage b.hom ≫ st)
      (U.1.fromPreimage b.hom)
      (by
        rw [Category.assoc, hg']
        exact (Subfunctor.fromPreimage_ι _ _).symm)
      (by rw [Category.assoc, ← Category.assoc st, hst, hs])
    show (U.1.preimage b.hom).ι ≫ g.hom ≫ (schemeTheoreticImageSubfunctor B S hS s).ι = _
    rw [← Category.assoc, h, Category.assoc, hst]

/-- **Stacks 0CPI.** Let `S` be a scheme, let `X`, `Y` be algebraic spaces over `S`, let
`U ⊆ W ⊆ Y` be open subspaces, and let `f : X ⟶ W` and `s : U ⟶ X` be morphisms with
`f ∘ s = id_U`. Assume that `f` is proper, that `Y` is quasi-compact and quasi-separated, and that
`U` and `W` are quasi-compact. Then there are a `U`-admissible blowup `b : Y' ⟶ Y` and a morphism
`s' : b⁻¹(W) ⟶ X` extending `s` with `f ∘ s' = b|_{b⁻¹(W)}`.

Here `W` is the algebraic space `AlgebraicGeometry.Space.openSubspace B S hS Y W`, so
`f ∘ s = id_U` reads `s ≫ f = U ↪ W`; quasi-separatedness of `Y` is absolute quasi-separatedness;
being a `U`-admissible blowup is Stacks 086B, `AlgebraicGeometry.Space.IsAdmissibleBlowup`;
`b⁻¹(W)` is the inverse image subfunctor `W.1.preimage b.hom`, and `b|_{b⁻¹(W)}` is
`W.1.fromPreimage b.hom`; and `s'` *extends* `s` in that its restriction to `b⁻¹(U) ⊆ b⁻¹(W)` is
`s ∘ b|_{b⁻¹(U)}` (the morphism `b⁻¹(U) ⟶ U` being an isomorphism, as `b` is `U`-admissible). -/
@[stacks 0CPI]
theorem exists_isAdmissibleBlowup_extending_section_of_isProper {X Y : AlgebraicSpaces B S hS}
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    (U W : OpenSubspaces B S hS Y.1) (hUW : U.1 ≤ W.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hWqc : IsQuasiCompactSpace B S hS W.1.toFunctor)
    (f : X ⟶ openSubspace B S hS Y W) (hf : IsProper B S hS f.hom)
    (s : U.1.toFunctor ⟶ X.1) (hs : s ≫ f.hom = Subfunctor.homOfLe hUW) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), IsAdmissibleBlowup B S hS U b ∧
      ∃ s' : (W.1.preimage b.hom).toFunctor ⟶ X.1, s' ≫ f.hom = W.1.fromPreimage b.hom ∧
        Subfunctor.homOfLe (fun T _ hx => hUW T hx :
          U.1.preimage b.hom ≤ W.1.preimage b.hom) ≫ s' = U.1.fromPreimage b.hom ≫ s := by
  have hZ := B.contains_terminal
  have hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1.toFunctor :=
    isAbsolutelyQuasiSeparated_subfunctor B S hS hZ hYqs W.1 W.2.1
  let U' : OpenSubspaces B S hS (openSubspace B S hS Y W).1 := openSubspaceRestrict B S hS Y W U
  have hU'qc : IsQuasiCompactSpace B S hS U'.1.toFunctor :=
    isQuasiCompactSpace_preimage_toFunctor B S hS hZ Y.2 hYqs W.2.1 hWqc U.1 hUqc W.1.ι
  let sW : U'.1.toFunctor ⟶ X.1 := U.1.fromPreimage W.1.ι ≫ s
  have hsW : sW ≫ f.hom = U'.1.ι := by
    rw [← cancel_mono W.1.ι]
    show (U.1.fromPreimage W.1.ι ≫ s) ≫ f.hom ≫ W.1.ι = (U.1.preimage W.1.ι).ι ≫ W.1.ι
    rw [Category.assoc, ← Category.assoc s, hs, Subfunctor.homOfLe_ι, Subfunctor.fromPreimage_ι]
  obtain ⟨W', bW, hbW, g, hg, hext⟩ :=
    dominatesSections_of_isQuasiCompactSpace (openSubspace B S hS Y W) hWqc hWqs U' hU'qc X f hf
      sW hsW
  have hg' : g.hom ≫ f.hom = bW.hom := congrArg (fun m => m.hom) hg
  -- extend the blowup of `W` to `Y` (Stacks 086D)
  obtain ⟨Y', b, hb, e, he⟩ :=
    exists_isAdmissibleBlowup_isPullback' hZ hYqc hYqs U W hUqc hWqc bW hbW
  have he' : IsPullback bW.hom e.hom W.1.ι b.hom := AlgebraicSpaces.isPullback_hom B S hS he
  let l : (W.1.preimage b.hom).toFunctor ⟶ W'.1 :=
    he'.lift (W.1.fromPreimage b.hom) (W.1.preimage b.hom).ι (Subfunctor.fromPreimage_ι _ _)
  have hl : l ≫ bW.hom = W.1.fromPreimage b.hom := he'.lift_fst _ _ _
  refine ⟨Y', b, hb, l ≫ g.hom, by rw [Category.assoc, hg', hl], ?_⟩
  have hle : U.1.preimage b.hom ≤ W.1.preimage b.hom := fun T _ hx => hUW T hx
  have key : Subfunctor.homOfLe hle ≫ l ≫ bW.hom ≫ W.1.ι = U.1.fromPreimage b.hom ≫ U.1.ι := by
    rw [← Category.assoc l, hl, Subfunctor.fromPreimage_ι, Subfunctor.homOfLe_ι_assoc,
      Subfunctor.fromPreimage_ι]
  let k : (U.1.preimage b.hom).toFunctor ⟶ (U'.1.preimage bW.hom).toFunctor :=
    Subfunctor.lift (Subfunctor.homOfLe hle ≫ l) (by
      rintro T _ ⟨x, rfl⟩
      show (bW.hom ≫ W.1.ι).app T ((Subfunctor.homOfLe hle ≫ l).app T x) ∈ U.1.obj T
      rw [← NatTrans.comp_app_apply, Category.assoc, key]
      exact ((U.1.fromPreimage b.hom).app T x).2)
  have hk : k ≫ (U'.1.preimage bW.hom).ι = Subfunctor.homOfLe hle ≫ l := Subfunctor.lift_ι _ _
  have hk' : k ≫ U'.1.fromPreimage bW.hom ≫ U.1.fromPreimage W.1.ι = U.1.fromPreimage b.hom := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, Subfunctor.fromPreimage_ι,
      ← Category.assoc (U'.1.fromPreimage bW.hom)]
    show k ≫ (U'.1.fromPreimage bW.hom ≫ U'.1.ι) ≫ W.1.ι = _
    rw [Subfunctor.fromPreimage_ι, ← key, Category.assoc, ← Category.assoc k, hk]
    simp only [Category.assoc]
  show Subfunctor.homOfLe hle ≫ l ≫ g.hom = _
  rw [← Category.assoc, ← hk, Category.assoc, hext, ← hk']
  simp only [sW, Category.assoc]

end AlgebraicGeometry.Space

end
