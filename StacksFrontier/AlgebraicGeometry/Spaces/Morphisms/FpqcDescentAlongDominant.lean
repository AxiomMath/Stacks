module

public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparatedEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Descending morphisms compatible with a scheme-theoretically dominant morphism

Let `π : T' ⟶ T` be a morphism of algebraic spaces over `S` which is an fpqc covering, let `X`,
`Y₁`, `Y₂` be algebraic spaces over `T` with `Y₂` separated over `T`, and let `cᵢ : X ⟶ Yᵢ` be
morphisms over `T`. Write `X'`, `Y₁'`, `Y₂'` and `c₁' : X' ⟶ Y₁'` for the base changes along `π`.
Suppose `c₁'` is quasi-compact and its scheme-theoretic image is all of `Y₁'`. Then a morphism
`ψ' : Y₁' ⟶ Y₂'` over `T'` with `c₁' ≫ ψ' = c₂'` is the base change of a unique morphism
`ψ : Y₁ ⟶ Y₂` over `T`, and `c₁ ≫ ψ = c₂`; if `ψ'` is an isomorphism and `Y₁` is separated over
`T` as well, so is `ψ`.

The descent condition of Stacks 04P2 for the morphism `Y₁' ⟶ Y₂` is checked on
`W = Y₁' ×_{Y₁} Y₁'`: the two morphisms `W ⟶ Y₂` agree after the base change of `c₁` to `W`,
because each projection `W ⟶ Y₁'` composed with it factors through `c₁'`, and that base change is
the base change of `c₁'` along the flat first projection `W ⟶ Y₁'`, so its scheme-theoretic image
is all of `W` by Stacks 089E; two morphisms into a separated space which agree after a morphism
with full scheme-theoretic image are equal (the argument of Stacks 084N).

This is the step of the proof of [Stacks, Tag 0E89] which replaces a Noetherian local base by its
completion; over the completion, the scheme-theoretic dominance of `c₁'` comes from
`𝒪 = c₁,*𝒪` on the special fibre.

## Main results

* `Space.eq_of_comp_eq_of_schemeTheoreticImageSubfunctor_eq_top`: two morphisms into a separated
  algebraic space agreeing after a morphism whose scheme-theoretic image is everything are equal.
* `Space.schemeTheoreticImageSubfunctor_comp_eq_top_of_isIso`: composing with an isomorphism keeps
  the scheme-theoretic image everything.
* `Space.eq_of_isFpqcCovering_of_comp_eq`: morphisms out of the target of a one-member fpqc
  covering are determined after the covering.
* `Space.exists_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top`: the descent of
  the morphism.
* `Space.exists_iso_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top`: the descent
  of the isomorphism.

## References

* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Two morphisms into a separated space agreeing after a morphism with full scheme-theoretic
image are equal.** Let `f, g : X ⟶ Y` be morphisms over `q : Y ⟶ T` with `q` separated and let
`d : D ⟶ X` have scheme-theoretic image all of `X`. If `d ≫ f = d ≫ g` then `f = g`: the
agreement locus of `f` and `g` is a closed subspace of `X` through which `d` factors, so it
contains the scheme-theoretic image of `d`. -/
theorem eq_of_comp_eq_of_schemeTheoreticImageSubfunctor_eq_top
    {T X Y D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (q : Y ⟶ T)
    (hq : IsSeparated B S hS q) {f g : X ⟶ Y} (hfg : f ≫ q = g ≫ q) (d : D ⟶ X)
    (hd : schemeTheoreticImageSubfunctor B S hS d = ⊤) (h : d ≫ f = d ≫ g) : f = g := by
  refine (eqSubfunctor_eq_top_iff B S hS q f g hfg).1 (top_le_iff.1 ?_)
  rw [← hd]
  refine schemeTheoreticImageSubfunctor_le B S hS d
    (isClosedSubspace_eqSubfunctor B S hS hT hX hY q f g hfg hq) ?_
  refine (le_eqSubfunctor_iff B S hS q f g hfg _).2 ?_
  rw [← cancel_epi (Subfunctor.toRange d), ← Category.assoc, Subfunctor.toRange_ι,
    ← Category.assoc, Subfunctor.toRange_ι, h]

/-- A base change of a one-member fpqc covering, presented by any cartesian square, is a
one-member fpqc covering (the one-member case of
`AlgebraicGeometry.Space.isFpqcCovering_of_isPullback`). -/
private theorem isFpqcCovering_unit_of_isPullback {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {π : Y' ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y'} (h : IsPullback p f' f π)
    (hπ : IsFpqcCovering B S hS (fun _ : Unit => π.hom)) :
    IsFpqcCovering B S hS (fun _ : Unit => p.hom) := by
  have h₁ := isFpqcCovering_pullback_fst B S hS _ (fun _ : Unit => π) hπ X f
  have h₂ := isFpqcCovering_isoComp B S hS (fun _ : Unit => (h.isoPullback.hom).hom)
    (fun _ => (pullback.fst f π).hom) h₁
  convert h₂ using 2
  exact congrArg (fun k : X' ⟶ X => k.hom) h.isoPullback_hom_fst.symm

/-- **Composing with an isomorphism keeps the scheme-theoretic image everything.** If the
scheme-theoretic image of `f : X ⟶ Y` is all of `Y` and `e : Y ⟶ Y'` is an isomorphism, the
scheme-theoretic image of `f ≫ e` is all of `Y'`: its inverse image along `e` is a closed subspace
containing the image of `f`. -/
theorem schemeTheoreticImageSubfunctor_comp_eq_top_of_isIso
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (e : Y ⟶ Y') [IsIso e]
    (hf : schemeTheoreticImageSubfunctor B S hS f = ⊤) :
    schemeTheoreticImageSubfunctor B S hS (f ≫ e) = ⊤ := by
  set Z := schemeTheoreticImageSubfunctor B S hS (f ≫ e)
  have hZ : IsClosedSubspace B S hS (Z.preimage e) :=
    isClosedSubspace_preimage B S hS e Z hY' hY
      (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (f ≫ e) hY')
  have hle : Subfunctor.range f ≤ Z.preimage e := by
    rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp]
    exact range_le_schemeTheoreticImageSubfunctor B S hS (f ≫ e)
  have htop : Z.preimage e = ⊤ :=
    top_le_iff.1 (hf ▸ schemeTheoreticImageSubfunctor_le B S hS f hZ hle)
  rw [Subfunctor.preimage_eq_top_iff, Subfunctor.range_eq_top] at htop
  exact top_le_iff.1 htop

/-- **Morphisms out of the target of a one-member fpqc covering are determined after the
covering**: the uniqueness half of Stacks 04P2. -/
theorem eq_of_isFpqcCovering_of_comp_eq {Y' Y Z : AlgebraicSpaces B S hS} {p : Y' ⟶ Y}
    (hp : IsFpqcCovering B S hS (fun _ : Unit => p.hom)) {u v : Y ⟶ Z} (h : p ≫ u = p ≫ v) :
    u = v := by
  obtain ⟨w, -, huniq⟩ := existsUnique_desc_of_fpqcCovering B S hS (fun _ : Unit => p) hp Z
    (fun _ => p ≫ u) (fun _ _ => by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS p p).w)
  exact (huniq u fun _ => rfl).trans (huniq v fun _ => h.symm).symm

/-- **A morphism of base changes compatible with a morphism of full scheme-theoretic image
descends.** Let `π : T' ⟶ T` be a one-member fpqc covering, `X`, `Y₁`, `Y₂` algebraic spaces over
`T` with `Y₂` separated over `T`, `cᵢ : X ⟶ Yᵢ` morphisms over `T`, and `X'`, `Y₁'`, `Y₂'` base
changes along `π` with `c₁' : X' ⟶ Y₁'` the base change of `c₁`. If `c₁'` is quasi-compact with
scheme-theoretic image all of `Y₁'`, a morphism `ψ' : Y₁' ⟶ Y₂'` over `T'` with
`c₁' ≫ ψ' = c₂'` is the base change of a morphism `ψ : Y₁ ⟶ Y₂` over `T`, and `c₁ ≫ ψ = c₂`. -/
theorem exists_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top
    {T T' X Y₁ Y₂ X' Y₁' Y₂' : AlgebraicSpaces B S hS} {π : T' ⟶ T}
    (hπ : IsFpqcCovering B S hS (fun _ : Unit => π.hom))
    {f : X ⟶ T} {g₁ : Y₁ ⟶ T} {g₂ : Y₂ ⟶ T} (hg₂ : IsSeparated B S hS g₂.hom)
    {pX : X' ⟶ X} {f' : X' ⟶ T'} (hX : IsPullback pX f' f π)
    {p₁ : Y₁' ⟶ Y₁} {g₁' : Y₁' ⟶ T'} (hY₁ : IsPullback p₁ g₁' g₁ π)
    {p₂ : Y₂' ⟶ Y₂} {g₂' : Y₂' ⟶ T'} (hY₂ : p₂ ≫ g₂ = g₂' ≫ π)
    {c₁ : X ⟶ Y₁} (hc₁ : c₁ ≫ g₁ = f) {c₂ : X ⟶ Y₂}
    {c₁' : X' ⟶ Y₁'} (hc₁'p : c₁' ≫ p₁ = pX ≫ c₁) (hc₁'g : c₁' ≫ g₁' = f')
    (hqc : IsQuasiCompact B S hS c₁'.hom)
    (hdom : schemeTheoreticImageSubfunctor B S hS c₁'.hom = ⊤)
    {ψ' : Y₁' ⟶ Y₂'} (hψ' : ψ' ≫ g₂' = g₁') (hψ'c : c₁' ≫ ψ' ≫ p₂ = pX ≫ c₂) :
    ∃ ψ : Y₁ ⟶ Y₂, ψ ≫ g₂ = g₁ ∧ p₁ ≫ ψ = ψ' ≫ p₂ ∧ c₁ ≫ ψ = c₂ := by
  have hp₁ := isFpqcCovering_unit_of_isPullback hY₁ hπ
  have hpX := isFpqcCovering_unit_of_isPullback hX hπ
  -- `X'` is the base change of `X` along `p₁`
  have sq : IsPullback pX c₁' c₁ p₁ := by
    refine IsPullback.of_bot ?_ hc₁'p.symm hY₁
    rw [hc₁'g, hc₁]
    exact hX
  have sqh := AlgebraicSpaces.isPullback_hom B S hS sq
  -- the two projections of `W = Y₁' ×_{Y₁} Y₁'`
  set W := AlgebraicSpaces.fiberProduct B S hS p₁ p₁
  set pr₁ : W ⟶ Y₁' := ObjectProperty.homMk (pullback.fst p₁.hom p₁.hom)
  set pr₂ : W ⟶ Y₁' := ObjectProperty.homMk (pullback.snd p₁.hom p₁.hom)
  have hW : pr₁ ≫ p₁ = pr₂ ≫ p₁ := (AlgebraicSpaces.isPullback_fiberProduct B S hS p₁ p₁).w
  have hflat : IsFlat B S hS pr₁.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS p₁ p₁).flip (hp₁.1 ())
  -- the base change `d` of `c₁'` to `W` has scheme-theoretic image everything (Stacks 089E)
  set d := pullback.snd c₁'.hom pr₁.hom
  have hd : schemeTheoreticImageSubfunctor B S hS d = ⊤ := by
    rw [schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact B S hS pr₁ c₁'
      hflat hqc, hdom]
    rfl
  have hT : (ψ' ≫ p₂) ≫ g₂ = p₁ ≫ g₁ := by
    rw [Category.assoc, hY₂, ← Category.assoc, hψ', hY₁.w]
  -- the descent condition
  have hdesc : pr₁ ≫ ψ' ≫ p₂ = pr₂ ≫ ψ' ≫ p₂ := by
    have hfg : (pr₁ ≫ ψ' ≫ p₂).hom ≫ g₂.hom = (pr₂ ≫ ψ' ≫ p₂).hom ≫ g₂.hom := by
      show ((pr₁ ≫ ψ' ≫ p₂) ≫ g₂).hom = ((pr₂ ≫ ψ' ≫ p₂) ≫ g₂).hom
      rw [Category.assoc, Category.assoc pr₂, hT, ← Category.assoc, ← Category.assoc, hW]
    refine ObjectProperty.hom_ext _ (eq_of_comp_eq_of_schemeTheoreticImageSubfunctor_eq_top
      T.2 W.2 Y₂.2 g₂.hom hg₂ hfg d hd ?_)
    have h₁ : d ≫ pr₁.hom = pullback.fst c₁'.hom pr₁.hom ≫ c₁'.hom := pullback.condition.symm
    have hcond : (pullback.fst c₁'.hom pr₁.hom ≫ pX.hom) ≫ c₁.hom =
        (d ≫ pr₂.hom) ≫ p₁.hom := by
      have h := congrArg (fun k => k.hom) hc₁'p
      have h' := congrArg (fun k => k.hom) hW
      simp only [ObjectProperty.FullSubcategory.comp_hom] at h h'
      rw [Category.assoc, ← h, ← Category.assoc, ← h₁, Category.assoc, h', Category.assoc]
    set e := sqh.lift _ _ hcond
    have he₁ : e ≫ pX.hom = pullback.fst c₁'.hom pr₁.hom ≫ pX.hom := sqh.lift_fst _ _ _
    have he₂ : e ≫ c₁'.hom = d ≫ pr₂.hom := sqh.lift_snd _ _ _
    have hc := congrArg (fun k => k.hom) hψ'c
    simp only [ObjectProperty.FullSubcategory.comp_hom] at hc ⊢
    rw [← Category.assoc, h₁, Category.assoc, hc, ← Category.assoc d, ← he₂, Category.assoc,
      hc, ← Category.assoc e, he₁, Category.assoc]
  obtain ⟨ψ, hψ, -⟩ := existsUnique_desc_of_fpqcCovering B S hS (fun _ : Unit => p₁) hp₁ Y₂
    (fun _ => ψ' ≫ p₂) (fun _ _ => hdesc)
  have hψ₁ : p₁ ≫ ψ = ψ' ≫ p₂ := hψ ()
  refine ⟨ψ, eq_of_isFpqcCovering_of_comp_eq hp₁ ?_, hψ₁,
    eq_of_isFpqcCovering_of_comp_eq hpX ?_⟩
  · rw [← Category.assoc, hψ₁, hT]
  · rw [← Category.assoc, ← hc₁'p, Category.assoc, hψ₁, hψ'c]

/-- **An isomorphism of base changes compatible with a morphism of full scheme-theoretic image
descends to an isomorphism.** Under the hypotheses of
`AlgebraicGeometry.Space.exists_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top`,
with `Y₁` separated over `T` as well and `Y₂'` a base change of `Y₂`, an isomorphism
`ψ' : Y₁' ≅ Y₂'` over `T'` with `c₁' ≫ ψ' = c₂'` is the base change of an isomorphism
`ψ : Y₁ ≅ Y₂` over `T`, and `c₁ ≫ ψ = c₂`. The inverse is descended in the same way, along the
base change `c₁' ≫ ψ'` of `c₂`, whose scheme-theoretic image is everything as well. -/
theorem exists_iso_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top
    {T T' X Y₁ Y₂ X' Y₁' Y₂' : AlgebraicSpaces B S hS} {π : T' ⟶ T}
    (hπ : IsFpqcCovering B S hS (fun _ : Unit => π.hom))
    {f : X ⟶ T} {g₁ : Y₁ ⟶ T} {g₂ : Y₂ ⟶ T} (hg₁ : IsSeparated B S hS g₁.hom)
    (hg₂ : IsSeparated B S hS g₂.hom)
    {pX : X' ⟶ X} {f' : X' ⟶ T'} (hX : IsPullback pX f' f π)
    {p₁ : Y₁' ⟶ Y₁} {g₁' : Y₁' ⟶ T'} (hY₁ : IsPullback p₁ g₁' g₁ π)
    {p₂ : Y₂' ⟶ Y₂} {g₂' : Y₂' ⟶ T'} (hY₂ : IsPullback p₂ g₂' g₂ π)
    {c₁ : X ⟶ Y₁} (hc₁ : c₁ ≫ g₁ = f) {c₂ : X ⟶ Y₂} (hc₂ : c₂ ≫ g₂ = f)
    {c₁' : X' ⟶ Y₁'} (hc₁'p : c₁' ≫ p₁ = pX ≫ c₁) (hc₁'g : c₁' ≫ g₁' = f')
    (hqc : IsQuasiCompact B S hS c₁'.hom)
    (hdom : schemeTheoreticImageSubfunctor B S hS c₁'.hom = ⊤)
    (ψ' : Y₁' ≅ Y₂') (hψ' : ψ'.hom ≫ g₂' = g₁') (hψ'c : c₁' ≫ ψ'.hom ≫ p₂ = pX ≫ c₂) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ g₂ = g₁ ∧ p₁ ≫ ψ.hom = ψ'.hom ≫ p₂ ∧ c₁ ≫ ψ.hom = c₂ := by
  obtain ⟨ψ, hψg, hψp, hψc⟩ :=
    exists_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top hπ hg₂ hX hY₁ hY₂.w
      hc₁ hc₁'p hc₁'g hqc hdom hψ' hψ'c
  have : IsIso ψ'.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map ψ'.hom))
  have hqc₂ : IsQuasiCompact B S hS (c₁' ≫ ψ'.hom).hom :=
    isQuasiCompact_comp B S hS Y₁'.2 Y₂'.2 _ _ hqc fun Z _ hqcZ g => by
      have : IsIso (pullback.fst g ψ'.hom.hom) :=
        (IsPullback.of_hasPullback g _).isIso_fst_of_isIso
      exact hqcZ.of_iso B S hS (asIso (pullback.fst g ψ'.hom.hom)).symm
  have hdom₂ : schemeTheoreticImageSubfunctor B S hS (c₁' ≫ ψ'.hom).hom = ⊤ :=
    schemeTheoreticImageSubfunctor_comp_eq_top_of_isIso Y₁'.2 Y₂'.2 c₁'.hom ψ'.hom.hom hdom
  obtain ⟨φ, -, hφp, -⟩ :=
    exists_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top hπ hg₁ hX hY₂ hY₁.w
      hc₂ (c₁' := c₁' ≫ ψ'.hom) (by rw [Category.assoc, hψ'c])
      (by rw [Category.assoc, hψ', hc₁'g]) hqc₂ hdom₂ (ψ' := ψ'.inv)
      (by rw [Iso.inv_comp_eq, hψ']) (by rw [Category.assoc, Iso.hom_inv_id_assoc, hc₁'p])
  have hp₁ := isFpqcCovering_unit_of_isPullback hY₁ hπ
  have hp₂ := isFpqcCovering_unit_of_isPullback hY₂ hπ
  refine ⟨⟨ψ, φ, eq_of_isFpqcCovering_of_comp_eq hp₁ ?_, eq_of_isFpqcCovering_of_comp_eq hp₂ ?_⟩,
    hψg, hψp, hψc⟩
  · rw [reassoc_of% hψp, hφp, Iso.hom_inv_id_assoc, Category.comp_id]
  · rw [reassoc_of% hφp, hψp, Iso.inv_hom_id_assoc, Category.comp_id]

end AlgebraicGeometry.Space

end
