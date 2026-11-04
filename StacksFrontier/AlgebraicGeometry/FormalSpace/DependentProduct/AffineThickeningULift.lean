module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.ChartBound
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.ColimitAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase

/-!
# A thickening over an affine base of an affine algebraic space, in the value universe of formal
algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `k : T₀ ⟶ T` be a thickening of affine
objects of the site and let `Q ⟶ h_T` be a morphism of fppf sheaves of `Type (u + 1)` whose source
is an algebraic space. If the base change `Q ×_{h_T} h_{T₀}` is represented by an affine object of
the site, then so is `Q`. This is
`AlgebraicGeometry.Space.isAffineSpace_of_isAffineSpace_pullback_of_isThickening` transported to
the value universe of the formal algebraic spaces, the algebraic space being the universe lift of
a presheaf of `Type u`.

## Main results

* `AlgebraicGeometry.FormalSpace.DependentProduct.exists_iso_uliftYoneda_of_isPullback_isThickening`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space over an affine object of the site whose base change along a thickening
of that object is affine is affine**, in the value universe of the formal algebraic spaces. -/
theorem exists_iso_uliftYoneda_of_isPullback_isThickening {Q Q₀ : FppfSheaf B S hS}
    (hQ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Q.obj) {T₀ T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (π : Q ⟶ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T)
    (π₀ : Q₀ ⟶ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T₀) (ι : Q₀ ⟶ Q)
    (hsq : IsPullback ι π₀ π ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k))
    {A₀ : BigFppfOver B S hS} (hA₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj A₀))
    (e₀ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj A₀ ≅ Q₀) :
    ∃ A : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      Nonempty ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj A ≅ Q) := by
  set J := BigFppfOver.topology B S hS with hJ
  set H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1} with hH
  have hHff : H.FullyFaithful := Space.uliftWhiskeringFullyFaithful B S hS
  have : H.Full := hHff.full
  have : H.Faithful := hHff.faithful
  obtain ⟨G, ⟨eG⟩⟩ := Space.exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hQ
  have hG : IsAlgebraicSpace B S hS G :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS G).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS eG.symm hQ)
  set π' : G ⟶ yoneda.obj T := H.preimage (eG.hom ≫ π.hom) with hπ'
  have hHπ' : H.map π' = eG.hom ≫ π.hom := H.map_preimage _
  -- the base change of `π'` along `k` is the affine object `A₀`
  have hpre : IsPullback (ι.hom ≫ eG.inv) π₀.hom (H.map π') (H.map (yoneda.map k)) := by
    rw [hHπ']
    have h1 := hsq.map (sheafToPresheaf J (Type (u + 1)))
    refine h1.of_iso (Iso.refl _) eG.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · show π.hom ≫ 𝟙 _ = eG.inv ≫ eG.hom ≫ π.hom
      rw [Iso.inv_hom_id_assoc, Category.comp_id]
    · rfl
  have : PreservesLimitsOfShape WalkingCospan H := inferInstance
  have hHpb := (IsPullback.of_hasPullback π' (yoneda.map k)).map H
  have e₁ : H.obj (pullback π' (yoneda.map k)) ≅ H.obj (yoneda.obj A₀) :=
    hHpb.isoIsPullback _ _ hpre ≪≫ (sheafToPresheaf J (Type (u + 1))).mapIso e₀.symm
  have hU₀ : Space.IsAffineSpace B S hS (pullback π' (yoneda.map k)) :=
    ⟨A₀, hA₀, ⟨hHff.preimageIso e₁⟩⟩
  obtain ⟨A, hA, ⟨eA⟩⟩ :=
    Space.isAffineSpace_of_isAffineSpace_pullback_of_isThickening B S hS hG hT k hk π' hU₀
  refine ⟨A, hA, ⟨(fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso ?_⟩⟩
  exact (H.mapIso eA).symm ≪≫ eG

/-- A monomorphism of fppf sheaves is injective on sections. -/
theorem injective_app_of_mono {X Y : FppfSheaf B S hS} (f : X ⟶ Y) [Mono f]
    (T : BigFppfOver B S hS) : Function.Injective (f.hom.app (Opposite.op T)) := by
  have : Mono ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map f) :=
    inferInstance
  exact (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this (Opposite.op T))

/-- **The dependent product of an affine étale chart along a composite of two base changes of
thickenings of affine objects is represented by an affine object.** Let `β : E₀ ⟶ E₁` be a base
change of `h_{k_A}` and `σ : E₁ ⟶ E₂` a base change of `h_{k_B}`, for thickenings
`k_A : A₀ ⟶ A` and `k_B : B₀ ⟶ B'` of objects of the site with affine targets, the sheaves `E₁` and
`E₂` being algebraic spaces. Then for an affine étale chart `c : h_W ⟶ E₀` the dependent product
`Π_{β ≫ σ} h_W` is represented by an affine object: it is affine over `B'` after base change to
`B₀`, where it is `Π_β h_W`, which is affine over `A` after base change to `A₀`, where it is
`h_W`. Each step is the affineness of a thickening over an affine base. -/
theorem exists_iso_uliftYoneda_liftAlong_comp {E₀ E₁ E₂ : FppfSheaf B S hS} (β : E₀ ⟶ E₁)
    (σ : E₁ ⟶ E₂) {A₀ A B₀ B' : BigFppfOver B S hS}
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (hB : IsAffine ((BigFppfOver.toScheme B S hS).obj B'))
    (kA : A₀ ⟶ A) (hkA : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map kA))
    (kB : B₀ ⟶ B') (hkB : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map kB))
    (p₀ : E₀ ⟶ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj A₀)
    (p₁ : E₁ ⟶ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj A)
    (hβ : IsPullback β p₀ p₁ ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map kA))
    (q₁ : E₁ ⟶ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj B₀)
    (q₂ : E₂ ⟶ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj B')
    (hσ : IsPullback σ q₁ q₂ ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map kB))
    (hE₁ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS E₁.obj)
    (hE₂ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS E₂.obj)
    {W : BigFppfOver B S hS} (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ E₀)
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} c.hom) :
    ∃ N : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj N) ∧
      Nonempty ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj N ≅
        liftAlong B S hS (β ≫ σ) c) := by
  set P := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) with hP
  have : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have : P.IsStableUnderBaseChange := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
  have hrelβ : P.relative (BigFppfOver.topology B S hS).uliftYoneda.{u + 1} β :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hβ.flip
      (MorphismProperty.relative_map hkA)
  have hrelσ : P.relative (BigFppfOver.topology B S hS).uliftYoneda.{u + 1} σ :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hσ.flip
      (MorphismProperty.relative_map hkB)
  have : Mono β := mono_of_relative_isThickening β hrelβ
  have : Mono σ := mono_of_relative_isThickening σ hrelσ
  have hcb := isEtaleChartBounded_of_relative c hc
  -- the dependent product along `β`
  have hrepβ := isRepresentableEtale_liftAlongBase β c
    (isAffineThickeningOver_of_relative β hrelβ) (chartBound_monotone W)
    (fun _ hκ ↦ chartBound_lt W hκ) hcb
  have halgβ := isAlgebraicSpaceULift_of_isRepresentableByAlgebraicSpacesULift _ hrepβ.1 hE₁
  have hsec := isPullback_liftAlongSection B S hS (injective_app_of_mono β) (p := c)
  obtain ⟨N', hN', ⟨e'⟩⟩ := exists_iso_uliftYoneda_of_isPullback_isThickening halgβ hA kA hkA
    (liftAlongBase B S hS β c ≫ p₁) (c ≫ p₀) _ (hsec.paste_vert hβ) hW (Iso.refl _)
  -- the dependent product along `β ≫ σ`
  have hrelβσ : P.relative (BigFppfOver.topology B S hS).uliftYoneda.{u + 1} (β ≫ σ) :=
    MorphismProperty.comp_mem _ _ _ hrelβ hrelσ
  have hrep := isRepresentableEtale_liftAlongBase (β ≫ σ) c
    (isAffineThickeningOver_of_relative _ hrelβσ) (chartBound_monotone W)
    (fun _ hκ ↦ chartBound_lt W hκ) hcb
  have halg := isAlgebraicSpaceULift_of_isRepresentableByAlgebraicSpacesULift _ hrep.1 hE₂
  exact exists_iso_uliftYoneda_of_isPullback_isThickening halg hB kB hkB
    (liftAlongBase B S hS (β ≫ σ) c ≫ q₂) (liftAlongBase B S hS β c ≫ q₁) _
    ((isPullback_liftAlong_comp_mono β σ c).paste_vert hσ) hN' e'

end AlgebraicGeometry.FormalSpace.DependentProduct

end
