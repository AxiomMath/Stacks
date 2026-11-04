module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldSections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres

/-!
# A field-valued point of an algebraic space has only as many lifts to a chart as the fibre
degree allows

The valuative-criterion step in the proof of Stacks 089J reads a point of the dense open `V`
with values in the fraction field `K` of a valuation ring as `d` *distinct* morphisms
`Spec K ⟶ W` from the chart lying over one `K`-point of the algebraic space, and then needs
that these `d` morphisms are **all** of them: after enlarging the valuation ring one obtains a
further morphism `Spec K' ⟶ W` over the same point of the space, and the argument proceeds by
matching it with one of the `d`.

That matching is what this file supplies. A morphism `T ⟶ W` over `ξ : yoneda.obj T ⟶ X` is
the same thing as a section of the fibre `V ⟶ T` of the chart at `ξ`, the fibre at a
field-valued point is finite locally free of rank bounded by the fibre-degree bound of Stacks
03JL, and a finite locally free morphism of rank `r` to the spectrum of a field has at most `r`
sections — which is
`Stacks.Morphisms.exists_eq_of_isFiniteLocallyFreeOfRank`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_eq_of_isFiniteLocallyFreeOfRank_fibre`: **as many pairwise
  distinct lifts of a field-valued point to the chart as the fibre degree allows are all the
  lifts.** Stated for a fibre presented as a cartesian square with finite locally free
  projection, which is the presentation Stacks 03JL uses.
* `AlgebraicGeometry.Space.exists_eq_of_hasUniversallyBoundedFibers`: the same with the fibre
  degree replaced by the universal bound of Stacks 03JL, so that one integer works for every
  field-valued point at once.
* `AlgebraicGeometry.Space.le_of_injective_lifts_of_isFiniteLocallyFreeOfRank_fibre`: **a
  field-valued point has at most as many pairwise distinct lifts to the chart as the fibre
  degree**, the cardinality statement behind the exhaustion.
* `AlgebraicGeometry.Space.exists_forall_le_of_hasUniversallyBoundedFibers`: the same with the
  fibre degree replaced by the universal bound of Stacks 03JL.

## What is and is not proved

Stacks 089J is **not** proved here and no declaration in this file carries a Stacks attribute:
Stacks 03JL is carried by `AlgebraicGeometry.Space.HasUniversallyBoundedFibers`, and the
counting of sections is Mathlib's `card_algHom_le_finrank`, which carries Tag 09HS upstream.

What is **not** proved is the valuative lifting condition for the morphism `X' ⟶ X` of Stacks
089J. The three inputs of that condition are the distinctness of the `d` projections, which is
`AlgebraicGeometry.Space.SpacesEtale.comp_yoneda_map_diagonalComplementProj_ne`; the
enlargement of the valuation ring, which is Stacks 089F in the form
`AlgebraicGeometry.Space.exists_valuationRing_extension_lift_of_isFlat`; and the matching of
the enlarged lift with one of the projections, which is what is proved here. Assembling the
three into a lift of the valuative square, through the proper projections of the fibre power,
is not done; see the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ProperRefinedValuative`.

Nothing is claimed about the images in the point set of the chart. Two distinct lifts of a
field-valued point may share their image point, so a count of points of `|W|` would not do; it
is the *morphisms* that are counted, as in
`StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementDistinct`.

## References

* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 089F](https://stacks.math.columbia.edu/tag/089F)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Lifts of `ξ` to the chart embed injectively into the sections of the fibre over `Spec K`. -/
private theorem exists_injective_lifts_to_sections
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X)
    {K : Type u} [Field K] (T : BigFppfOver B S hS)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
    (ξ : yoneda.obj T ⟶ X) (V : BigFppfOver B S hS) (p : V ⟶ T)
    (i : yoneda.obj V ⟶ yoneda.obj W) (hsq : IsPullback i (yoneda.map p) c ξ) :
    ∃ f : {m : T ⟶ W // yoneda.map m ≫ c = ξ} →
        {σ : Spec (CommRingCat.of K) ⟶ (BigFppfOver.toScheme B S hS).obj V //
          σ ≫ (BigFppfOver.toScheme B S hS).map p ≫ eT.hom = 𝟙 _},
      Function.Injective f := by
  -- a morphism `T ⟶ W` over `ξ` is a section of the fibre `V ⟶ T`
  have hsec : ∀ m : T ⟶ W, yoneda.map m ≫ c = ξ →
      ∃ s : T ⟶ V, s ≫ p = 𝟙 T ∧ yoneda.map s ≫ i = yoneda.map m := by
    intro m hm
    refine ⟨yoneda.preimage (hsq.lift (yoneda.map m) (𝟙 _) (by rw [hm, Category.id_comp])), ?_,
      ?_⟩
    · refine yoneda.map_injective ?_
      rw [CategoryTheory.Functor.map_comp, yoneda.map_preimage, hsq.lift_snd]
      exact (CategoryTheory.Functor.map_id yoneda T).symm
    · rw [yoneda.map_preimage, hsq.lift_fst]
  choose s hs₁ hs₂ using hsec
  refine ⟨fun m ↦ ⟨eT.inv ≫ (BigFppfOver.toScheme B S hS).map (s m.1 m.2), ?_⟩, ?_⟩
  · rw [Category.assoc, ← Category.assoc ((BigFppfOver.toScheme B S hS).map (s m.1 m.2)),
      ← CategoryTheory.Functor.map_comp, hs₁, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id]
  · intro m m' h
    have h2 : s m.1 m.2 = s m'.1 m'.2 :=
      (BigFppfOver.toScheme B S hS).map_injective ((cancel_epi eT.inv).1 (congrArg Subtype.val h))
    refine Subtype.ext (yoneda.map_injective ?_)
    rw [← hs₂ m.1 m.2, ← hs₂ m'.1 m'.2, h2]

/-- **As many pairwise distinct lifts of a field-valued point to a chart as the fibre degree
allows are all the lifts.**

The data is that of Stacks 03JL: a morphism `c : yoneda.obj W ⟶ X` from an object of the site,
a field-valued point `ξ` of `X` — an object `T` of the site whose underlying scheme is
identified with `Spec K` for a field `K`, together with a morphism `yoneda.obj T ⟶ X` — and a
cartesian square presenting the fibre of `c` at `ξ` as an object `V` of the site with
`p : V ⟶ T` finite locally free of rank `r`.

The conclusion is that `n` pairwise distinct morphisms `T ⟶ W` over `ξ`, with `n ≥ r`, exhaust
the morphisms `T ⟶ W` over `ξ`.

A morphism `m : T ⟶ W` with `yoneda.map m ≫ c = ξ` factors uniquely through the cartesian
square as a section of `p`, so the statement reduces to the count of sections of a finite
locally free morphism to the spectrum of a field, which is
`Stacks.Morphisms.exists_eq_of_isFiniteLocallyFreeOfRank`. -/
theorem exists_eq_of_isFiniteLocallyFreeOfRank_fibre
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X)
    {K : Type u} [Field K] (T : BigFppfOver B S hS)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
    (ξ : yoneda.obj T ⟶ X) (V : BigFppfOver B S hS) (p : V ⟶ T)
    (i : yoneda.obj V ⟶ yoneda.obj W) (r n : ℕ)
    (hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map p) r)
    (hsq : IsPullback i (yoneda.map p) c ξ) (hrn : r ≤ n)
    (w : Fin n → (T ⟶ W)) (hw : ∀ k, yoneda.map (w k) ≫ c = ξ) (hwinj : Function.Injective w)
    (v : T ⟶ W) (hv : yoneda.map v ≫ c = ξ) :
    ∃ k, v = w k := by
  obtain ⟨f, hf⟩ := exists_injective_lifts_to_sections B S hS W c T eT ξ V p i hsq
  have hg : Function.Injective fun k ↦ f ⟨w k, hw k⟩ :=
    hf.comp fun a b h ↦ hwinj (congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := Stacks.Morphisms.exists_eq_of_isFiniteLocallyFreeOfRank _ r n
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_postcomp eT _ hr) hrn
    (fun k ↦ (f ⟨w k, hw k⟩).1) (fun k ↦ (f _).2) (fun a b hab ↦ hg (Subtype.ext hab)) _
    (f ⟨v, hv⟩).2
  exact ⟨k, congrArg Subtype.val (hf (Subtype.ext hk))⟩

/-- **A chart with universally bounded fibres has one bound beyond which distinct lifts of a
field-valued point are impossible, so that as many distinct lifts as the bound allows are all
the lifts.**

This is `AlgebraicGeometry.Space.exists_eq_of_isFiniteLocallyFreeOfRank_fibre` with the fibre
produced by the universal bound of Stacks 03JL instead of being supplied: the bound of Stacks
03JL is an integer `n` dominating the degree of every field-valued fibre, so the natural number
it names works for every field-valued point of `X` at once.

This is the form in which the proof of Stacks 089J uses the statement: the integer `n` is the
degree bound of the chart, the `d` morphisms are the projections of the complement of the
diagonals, pairwise distinct by
`AlgebraicGeometry.Space.SpacesEtale.comp_yoneda_map_diagonalComplementProj_ne`, and the further
morphism is the lift produced by Stacks 089F after enlarging the valuation ring. -/
theorem exists_eq_of_hasUniversallyBoundedFibers
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X)
    (hbound : HasUniversallyBoundedFibers B S hS W c) :
    ∃ n : ℕ, ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (m : ℕ), n ≤ m → ∀ w : Fin m → (T ⟶ W),
        (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w →
          ∀ v : T ⟶ W, yoneda.map v ≫ c = ξ → ∃ k, v = w k := by
  obtain ⟨n, hn⟩ := hbound
  refine ⟨n.toNat, fun K hK T eT ξ m hm w hw hwinj v hv ↦ ?_⟩
  obtain ⟨V, p, i, r, hrle, hrank, hsq⟩ := hn K T eT ξ
  exact exists_eq_of_isFiniteLocallyFreeOfRank_fibre B S hS W c T eT ξ V p i r m hrank hsq
    (le_trans (by omega) hm) w hw hwinj v hv

/-- **A field-valued point of a chart has at most as many pairwise distinct lifts as the fibre
degree allows.**

The data is that of Stacks 03JL, as in
`AlgebraicGeometry.Space.exists_eq_of_isFiniteLocallyFreeOfRank_fibre`: a morphism
`c : yoneda.obj W ⟶ X`, a field-valued point `ξ` of `X` defined on an object `T` of the site
whose underlying scheme is identified with `Spec K`, and a cartesian square presenting the fibre
of `c` at `ξ` as an object `V` of the site with `p : V ⟶ T` finite locally free of rank `r`.

Each morphism `T ⟶ W` over `ξ` factors uniquely through the cartesian square as a section of
`p`, and distinct morphisms give distinct sections, so `n` pairwise distinct lifts produce `n`
distinct sections of a finite locally free morphism of rank `r` to the spectrum of a field,
of which there are at most `r` by
`Stacks.Morphisms.finite_and_card_sections_le_of_isFiniteLocallyFreeOfRank`. -/
theorem le_of_injective_lifts_of_isFiniteLocallyFreeOfRank_fibre
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X)
    {K : Type u} [Field K] (T : BigFppfOver B S hS)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
    (ξ : yoneda.obj T ⟶ X) (V : BigFppfOver B S hS) (p : V ⟶ T)
    (i : yoneda.obj V ⟶ yoneda.obj W) (r n : ℕ)
    (hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map p) r)
    (hsq : IsPullback i (yoneda.map p) c ξ)
    (w : Fin n → (T ⟶ W)) (hw : ∀ k, yoneda.map (w k) ≫ c = ξ)
    (hwinj : Function.Injective w) :
    n ≤ r := by
  obtain ⟨f, hf⟩ := exists_injective_lifts_to_sections B S hS W c T eT ξ V p i hsq
  have hg : Function.Injective fun k ↦ f ⟨w k, hw k⟩ :=
    hf.comp fun a b h ↦ hwinj (congrArg Subtype.val h)
  obtain ⟨_, hcard⟩ := Stacks.Morphisms.finite_and_card_sections_le_of_isFiniteLocallyFreeOfRank _ r
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_postcomp eT _ hr)
  calc n = Nat.card (Fin n) := (Nat.card_fin n).symm
    _ ≤ _ := Nat.card_le_card_of_injective _ hg
    _ ≤ r := hcard

/-- **A chart with universally bounded fibres has one bound on the number of pairwise distinct
lifts of every field-valued point.**

This is `AlgebraicGeometry.Space.le_of_injective_lifts_of_isFiniteLocallyFreeOfRank_fibre` with
the fibre produced by the universal bound of Stacks 03JL instead of being supplied: the bound of
Stacks 03JL is an integer dominating the degree of every field-valued fibre, so the natural
number it names bounds the lifts of every field-valued point of `X` at once. -/
theorem exists_forall_le_of_hasUniversallyBoundedFibers
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X)
    (hbound : HasUniversallyBoundedFibers B S hS W c) :
    ∃ d : ℕ, ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (n : ℕ) (w : Fin n → (T ⟶ W)),
        (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w → n ≤ d := by
  obtain ⟨N, hN⟩ := hbound
  refine ⟨N.toNat, fun K hK T eT ξ n w hw hwinj ↦ ?_⟩
  obtain ⟨V, p, i, r, hrle, hrank, hsq⟩ := hN K T eT ξ
  have hnr := le_of_injective_lifts_of_isFiniteLocallyFreeOfRank_fibre B S hS W c T eT ξ
    V p i r n hrank hsq w hw hwinj
  omega

end AlgebraicGeometry.Space

end
