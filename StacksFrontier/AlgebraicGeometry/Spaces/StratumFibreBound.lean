module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.OpenSubschemeRankBound
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyBoundedFibers

/-!
# Bounds on the fibres of a chart from the degree stratification

Let `f : h_V ⟶ X` be a relatively representable morphism of presheaves on the big fppf site over
`S`. The fibre of `f` over a field-valued point of `X` satisfies the *degree-at-least `d`
disjunction* if it either fails to be finite or is finite locally free of some rank at least `d`;
this is the condition describing the strata of [Stacks, Tag 086T]. If no field-valued point of
`X` satisfies the degree-at-least `n + 1` disjunction, then `f`, and its restriction along any
open immersion of the site, has universally bounded fibres with bound `n` in the sense of
[Stacks, Tag 03JL].

## Main results

* `AlgebraicGeometry.Space.schemeFibreDegreeGe_iff_presheafFibreDegreeGe`: the degree-at-least
  `d` disjunction read on the represented fibre of `f` as a morphism of schemes agrees with the
  same disjunction read on the categorical fibre product through the presheaf form of the two
  morphism properties.
* `AlgebraicGeometry.Space.not_presheafFibreDegreeGe_of_rank_le`: the negation of the
  degree-at-least `n + 1` disjunction holds of a fibre over the spectrum of a field which is
  finite locally free of a rank at most `n`.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_restrict_of_not_presheafFibreDegreeGe`:
  if no field-valued point of `X` satisfies the degree-at-least `n + 1` disjunction for `f`,
  then the restriction of `f` along an open immersion `j : W ⟶ V` of the site has universally
  bounded fibres, with bound `n`.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_not_presheafFibreDegreeGe`: the same
  statement for `f` itself.

## Implementation notes

The translation between the scheme and presheaf forms of the disjunction is
`AlgebraicGeometry.Space.presheafFibreProperty_iff_schemeFibreProperty`, applied to
`AlgebraicGeometry.IsFinite` and to each `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property r`;
both properties respect isomorphisms and are stable under base change. The instance
`CategoryTheory.MorphismProperty.RespectsIso` for `AlgebraicGeometry.IsFinite` is supplied
locally by `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`.

The fibre of the restricted chart over a field-valued point is the fibre product of `j` with the
structure morphism of the fibre of `f`, formed in the site; the site has pullbacks and the
forgetful functor to schemes preserves them, so that fibre is an open subscheme of the fibre of
`f`, and `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion_of_isFinite`
bounds its rank by the same `n`. The cartesian square which
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers` requires is the vertical paste of the site
pullback square, transported by `CategoryTheory.yoneda`, with the square representing the fibre
of `f`.

The rank bounds used are stated for a morphism to `Spec k`, whereas a field-valued point in
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers` is an object `T` of the site together with
an isomorphism `(BigFppfOver.toScheme B S hS).obj T ≅ Spec k`. The two are reconciled by
composing with that isomorphism and cancelling it again, both properties involved respecting
isomorphisms.

## References

* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_StratumFibreBound :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_StratumFibreBound
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- For a relatively representable morphism `f : h_V ⟶ X` of presheaves on the big fppf site
over `S` and a morphism `a : h_A ⟶ X`, the disjunction "the represented fibre of `f` along `a` is
not finite, or it is finite locally free of some rank at least `d`", read of the morphism of
schemes representing that fibre, is equivalent to the same disjunction read of the categorical
fibre product `h_A ×_X h_V` through the presheaf forms of the two properties. -/
theorem schemeFibreDegreeGe_iff_presheafFibreDegreeGe
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V A : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj A ⟶ X) (d : ℕ) :
    ((¬ _root_.AlgebraicGeometry.IsFinite
          ((BigFppfOver.toScheme B S hS).map (hf.snd a))) ∨
        ∃ r : ℕ, d ≤ r ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank
          ((BigFppfOver.toScheme B S hS).map (hf.snd a)) r) ↔
      ((¬ (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst a f)) ∨
        ∃ r : ℕ, d ≤ r ∧
          (MorphismProperty.inverseImage
            (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst a f)) := by
  have _hfinIso : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}))
  have hfin := presheafFibreProperty_iff_schemeFibreProperty B S hS
    (P := @_root_.AlgebraicGeometry.IsFinite.{u}) f hf a
  have hrank (r : ℕ) := presheafFibreProperty_iff_schemeFibreProperty B S hS
    (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r) f hf a
  exact or_congr (not_congr hfin.symm)
    (exists_congr fun r => and_congr_right fun _ => (hrank r).symm)

/-- Postcomposing with an isomorphism does not change whether a morphism is finite locally free of
rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_comp_hom_iff {X Y Z : Scheme.{u}} (g : Z ⟶ X)
    (e : X ≅ Y) (r : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (g ≫ e.hom) r ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank g r :=
  MorphismProperty.cancel_right_of_respectsIso
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r) g e.hom

/-- If the represented fibre of `f` along a morphism `a : h_A ⟶ X` whose underlying scheme is
the spectrum of a field is finite locally free of a rank at most `n`, then the degree-at-least
`n + 1` disjunction fails for it: the fibre is finite, and it is finite locally free of no rank
at least `n + 1`. -/
theorem not_presheafFibreDegreeGe_of_rank_le
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V A : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj A ⟶ X) {k : Type u} [Field k]
    (e : (BigFppfOver.toScheme B S hS).obj A ≅ Spec (.of k)) {n r : ℕ} (hrn : r ≤ n)
    (hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map (hf.snd a)) r) :
    ¬ ((¬ (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst a f)) ∨
        ∃ r' : ℕ, n + 1 ≤ r' ∧
          (MorphismProperty.inverseImage
            (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r')
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst a f)) := by
  rw [← schemeFibreDegreeGe_iff_presheafFibreDegreeGe B S hS f hf a (n + 1), not_or, not_not]
  refine ⟨((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    _).mp (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r (h := hr))).1, ?_⟩
  rintro ⟨r', hr', hflf⟩
  exact not_isFiniteLocallyFreeOfRank_of_rank_le
    ((BigFppfOver.toScheme B S hS).map (hf.snd a) ≫ e.hom)
    ((isFiniteLocallyFreeOfRank_comp_hom_iff _ e r).mpr hr) hrn r' hr'
    ((isFiniteLocallyFreeOfRank_comp_hom_iff _ e r').mpr hflf)

/-- If no fibre of a relatively representable morphism `f : h_V ⟶ X` over a field-valued point
of `X` satisfies the degree-at-least `n + 1` disjunction, then the restriction of `f` along an
open immersion `j : W ⟶ V` of the site has universally bounded fibres, with bound `n`. -/
theorem hasUniversallyBoundedFibers_restrict_of_not_presheafFibreDegreeGe
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (j : W ⟶ V)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (n : ℕ)
    (h : ∀ (k : Type u) (_ : Field k) (T : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        ¬ ((¬ (MorphismProperty.inverseImage
              (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst ξ f)) ∨
          ∃ r : ℕ, n + 1 ≤ r ∧
            (MorphismProperty.inverseImage
              (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst ξ f))) :
    HasUniversallyBoundedFibers B S hS W (yoneda.map j ≫ f) := by
  have _hT : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  have _hfinIso : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}))
  refine hasUniversallyBoundedFibers_of_bound B S hS W _ (n : ℤ) fun k _ T e ξ => ?_
  have hnot := h k ‹_› T e ξ
  rw [← schemeFibreDegreeGe_iff_presheafFibreDegreeGe B S hS f hf ξ (n + 1), not_or,
    not_not] at hnot
  obtain ⟨hfin, hrank⟩ := hnot
  obtain ⟨φ, hφ⟩ := yoneda.map_surjective (hf.fst ξ)
  have hmopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd j φ)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
      ((IsPullback.of_hasPullback j φ).map (BigFppfOver.toScheme B S hS)) hj
  have _hq : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hf.snd ξ) ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) e.hom _ hfin
  obtain ⟨r, hrn, hr⟩ := exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion_of_isFinite
    ((BigFppfOver.toScheme B S hS).map (hf.snd ξ) ≫ e.hom)
    ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd j φ)) n
    (fun r hr hcon =>
      hrank ⟨r, hr, (isFiniteLocallyFreeOfRank_comp_hom_iff _ e r).mp hcon⟩)
  have hsq : IsPullback (yoneda.map (Limits.pullback.fst j φ))
      (yoneda.map (Limits.pullback.snd j φ)) (yoneda.map j) (hf.fst ξ) :=
    hφ ▸ ((IsPullback.of_hasPullback j φ).map yoneda)
  refine ⟨Limits.pullback j φ, Limits.pullback.snd j φ ≫ hf.snd ξ,
    yoneda.map (Limits.pullback.fst j φ), r, by exact_mod_cast hrn, ?_, ?_⟩
  · refine (isFiniteLocallyFreeOfRank_comp_hom_iff _ e r).mp ?_
    rwa [CategoryTheory.Functor.map_comp, Category.assoc]
  · have hpaste := hsq.paste_vert (hf.isPullback ξ)
    rwa [← CategoryTheory.Functor.map_comp] at hpaste

/-- If no fibre of a relatively representable morphism `f : h_V ⟶ X` over a field-valued point
of `X` satisfies the degree-at-least `n + 1` disjunction, then `f` has universally bounded
fibres, with bound `n`. -/
theorem hasUniversallyBoundedFibers_of_not_presheafFibreDegreeGe
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f) (n : ℕ)
    (h : ∀ (k : Type u) (_ : Field k) (T : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        ¬ ((¬ (MorphismProperty.inverseImage
              (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst ξ f)) ∨
          ∃ r : ℕ, n + 1 ≤ r ∧
            (MorphismProperty.inverseImage
              (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst ξ f))) :
    HasUniversallyBoundedFibers B S hS V f := by
  have hid : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (𝟙 V)) := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have hres := hasUniversallyBoundedFibers_restrict_of_not_presheafFibreDegreeGe B S hS f hf
    (𝟙 V) hid n h
  rwa [CategoryTheory.Functor.map_id, Category.id_comp] at hres

end AlgebraicGeometry.Space

end
