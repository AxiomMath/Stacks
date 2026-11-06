module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.OpenSubschemeRankBound
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale

/-!
# Reasonableness of the source of an étale morphism

An algebraic space étale over a reasonable algebraic space is itself reasonable. This is the
reasonable half of **Stacks 0ABU**.

## Main results

* `AlgebraicGeometry.Space.isPullback_comparison_diagonal`: the fibre product of two
  presheaves over the source of a morphism `f` is the base change of the relative diagonal of
  `f` along their fibre product over its target.
* `AlgebraicGeometry.Space.isReasonableSpace_of_isEtale`: the source of an étale morphism of
  algebraic spaces over `S` whose target is reasonable is reasonable.

## Implementation notes

`AlgebraicGeometry.Space.IsReasonableSpace` spells Stacks 03I8 with condition (2) of
Stacks 03JT, universal boundedness of the fibres of every étale chart by an affine scheme, so
the argument of Stacks 0ABU is run on that condition directly. Composing an étale chart
`U ⟶ X` with `f` is an étale chart of `Y`, and the degree bound the target supplies for it is
transferred to the source one fibre at a time: over a field-valued point `ξ` of `X`, the fibre
`U ×_X ξ` is an open subscheme of the fibre `U ×_Y ξ`, because it is the base change of the
relative diagonal of `f`, which is an open immersion for an étale — hence unramified —
morphism. An open subscheme of a scheme finite locally free of rank `r` over a field is finite
locally free of rank at most `r`, so the same integer bounds both.

The source phrases this step as the monomorphism `U ×_X U ⟶ U ×_Y U`; the open immersion used
here is the stronger statement available for an étale morphism, and it is what makes the
degrees comparable rather than merely the point sets.

## References

* [Stacks Project, Tag 0ABU](https://stacks.math.columbia.edu/tag/0ABU)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Fibre products of presheaves of types on `BigFppfOver B S hS`, supplied explicitly: instance
search for them times out. -/
local instance (priority := high) {A₁ A₂ A₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g₁ : A₁ ⟶ A₃)
    (g₂ : A₂ ⟶ A₃) : HasLimit (cospan g₁ g₂) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-- The fibre product of `φ` and `ξ` over the source of `f` is the base change of the relative
diagonal of `f` along their fibre product over its target: `P` is the fibre product of `Q`
and `X` over `X ×_Y X`, along the morphism `m` with components `c ≫ φ` and `d ≫ ξ`. -/
theorem isPullback_comparison_diagonal {U T P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {φ : U ⟶ X} {ξ : T ⟶ X} {a : P ⟶ U} {b : P ⟶ T} (hP : IsPullback a b φ ξ)
    {c : Q ⟶ U} {d : Q ⟶ T} (hQ : IsPullback c d (φ ≫ f) (ξ ≫ f))
    (κ : P ⟶ Q) (hκc : κ ≫ c = a) (hκd : κ ≫ d = b)
    (m : Q ⟶ pullback f f) (hmfst : m ≫ pullback.fst f f = c ≫ φ)
    (hmsnd : m ≫ pullback.snd f f = d ≫ ξ) :
    IsPullback κ (a ≫ φ) m (pullback.diagonal f) := by
  have hw : κ ≫ m = (a ≫ φ) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, hmfst]
      rw [← Category.assoc, hκc]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, hmsnd]
      rw [← Category.assoc, hκd]
      exact hP.w.symm
  have hcone : ∀ s : PullbackCone m (pullback.diagonal f),
      (s.fst ≫ c) ≫ φ = s.snd ∧ (s.fst ≫ d) ≫ ξ = s.snd := by
    intro s
    have hs := s.condition
    constructor
    · have h := congrArg (fun t => t ≫ pullback.fst f f) hs
      simp only [Category.assoc, hmfst, pullback.diagonal_fst, Category.comp_id] at h
      simpa only [Category.assoc] using h
    · have h := congrArg (fun t => t ≫ pullback.snd f f) hs
      simp only [Category.assoc, hmsnd, pullback.diagonal_snd, Category.comp_id] at h
      simpa only [Category.assoc] using h
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => hP.lift (s.fst ≫ c) (s.fst ≫ d) (((hcone s).1).trans ((hcone s).2).symm))
    (fun s => ?_) (fun s => ?_) (fun s n hn₁ _ => ?_))
  · refine hQ.hom_ext ?_ ?_
    · rw [Category.assoc, hκc, hP.lift_fst]
    · rw [Category.assoc, hκd, hP.lift_snd]
  · rw [← Category.assoc, hP.lift_fst]
    exact (hcone s).1
  · refine hP.hom_ext ?_ ?_
    · rw [hP.lift_fst, ← hκc, ← Category.assoc, hn₁]
    · rw [hP.lift_snd, ← hκd, ← Category.assoc, hn₁]

/-- **Stacks 0ABU, the reasonable case.** An algebraic space over `S` étale over a reasonable
algebraic space over `S` is reasonable. -/
@[stacks 0ABU "reasonable"]
theorem isReasonableSpace_of_isEtale (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsEtale B S hS f)
    (hreas : IsReasonableSpace B S hS Y) :
    IsReasonableSpace B S hS X := by
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hΔ : IsOpenImmersion B S hS (pullback.diagonal f) :=
    isOpenImmersion_diagonal_of_isUnramified B S hS hX hY f (isUnramified_of_isEtale B S hS hf)
  intro U hU φ hφ
  obtain ⟨n, hn⟩ := hreas U hU (φ ≫ f) (hf U φ hφ)
  refine ⟨n, fun k _ T e ξ => ?_⟩
  obtain ⟨V, p, i, r, hrn, hrank, hV⟩ := hn k T e (ξ ≫ f)
  have hP : IsPullback (hφ.rep.fst ξ) (yoneda.map (hφ.rep.snd ξ)) φ ξ := hφ.rep.isPullback ξ
  -- The fibre over `X` sits inside the fibre over `Y` as the base change of the diagonal.
  have hlift : hφ.rep.fst ξ ≫ (φ ≫ f) = yoneda.map (hφ.rep.snd ξ) ≫ (ξ ≫ f) := by
    simp only [← Category.assoc, hP.w]
  have hcomp := isPullback_comparison_diagonal B S hS f hP hV
    (hV.lift _ _ hlift) (hV.lift_fst _ _ hlift) (hV.lift_snd _ _ hlift)
    (pullback.lift (i ≫ φ) (yoneda.map p ≫ ξ) (by simp only [Category.assoc]; exact hV.w))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hκopen : IsOpenImmersion B S hS (hV.lift _ _ hlift) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcomp.flip hΔ
  obtain ⟨ι, hι⟩ : ∃ ι : hφ.rep.pullback ξ ⟶ V, yoneda.map ι = hV.lift _ _ hlift :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ι).1 (by rw [hι]; exact hκopen)
  have hιp : ι ≫ p = hφ.rep.snd ξ :=
    yoneda.map_injective (by rw [Functor.map_comp, hι, hV.lift_snd _ _ hlift])
  -- An open subscheme of the fibre over `Y` has no larger degree.
  have hrk : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map p ≫ e.hom) r :=
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_postcomp e _ hrank
  obtain ⟨r', hr'r, hr'⟩ :=
    AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion
      ((BigFppfOver.toScheme B S hS).map p ≫ e.hom) ((BigFppfOver.toScheme B S hS).map ι) r
  have hswap : (BigFppfOver.toScheme B S hS).map ι ≫
      ((BigFppfOver.toScheme B S hS).map p ≫ e.hom) =
      (BigFppfOver.toScheme B S hS).map (hφ.rep.snd ξ) ≫ e.hom := by
    rw [← Category.assoc, ← Functor.map_comp, hιp]
  rw [hswap] at hr'
  refine ⟨hφ.rep.pullback ξ, hφ.rep.snd ξ, hφ.rep.fst ξ, r',
    (Nat.cast_le.mpr hr'r).trans hrn, ?_, hP⟩
  simpa using Stacks.Morphisms.isFiniteLocallyFreeOfRank_postcomp e.symm _ hr'

end AlgebraicGeometry.Space

end
