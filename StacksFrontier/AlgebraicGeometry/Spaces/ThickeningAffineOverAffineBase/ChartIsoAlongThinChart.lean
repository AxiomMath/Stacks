module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.EtaleIsoAlongSurjection

/-!
# A chart of an algebraic space identified with a base change, tested on a thin chart

Let `X` be an algebraic space over `S` with a surjective étale chart `w : h_W ⟶ X` and kernel
pair `s, t : R ⟶ W`.  Let `φ : X ⟶ h_Y` be a morphism to a represented presheaf, let
`ψ : Y' ⟶ Y` be étale, and let `β : W ⟶ Y'` lift `φ` on the chart.  The induced morphism
`h_W ⟶ X ×_Y Y'` is a morphism of algebraic spaces étale over `X`.  To see that it is an
isomorphism it suffices, by the descent of isomorphisms along a surjection, to see it after base
change along `h_{W₀} ⟶ h_W ⟶ X` for a surjective `ι₀ : W₀ ⟶ W`, and that base change is the
morphism of schemes `W₀ ×_W R ⟶ W₀ ×_Y Y'` with components the first projection and
`t ≫ β`.  In particular `X ×_Y Y'` is then an affine algebraic space if `W` is affine.

## Main results

* `AlgebraicGeometry.Space.isIso_lift_of_isIso_thin`: the induced morphism is an isomorphism.
* `AlgebraicGeometry.Space.isAffineSpace_pullback_of_isIso_thin`: `X ×_Y Y'` is affine.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  {W : BigFppfOver B S hS} (w : yoneda.obj W ⟶ X)
  (hwe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w)
  {Y Y' : BigFppfOver B S hS} (φ : X ⟶ yoneda.obj Y) (ψ : Y' ⟶ Y)
  [Etale ((BigFppfOver.toScheme B S hS).map ψ)]
  (β : W ⟶ Y') (hβ : w ≫ φ = yoneda.map (β ≫ ψ))
  {O₀ W₀ : BigFppfOver B S hS} (x₀ : yoneda.obj O₀ ⟶ X) (ι₀ : W₀ ⟶ W) (c₀ : W₀ ⟶ O₀)
  (hsq₀ : IsPullback (yoneda.map ι₀) (yoneda.map c₀) w x₀)

/-- Pullbacks of presheaves on `BigFppfOver B S hS` (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_chartIsoAlongThinChart
    {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The morphism `O₀ ⟶ Y` underlying `x₀ ≫ φ`. -/
def thinBase : O₀ ⟶ Y := yoneda.preimage (x₀ ≫ φ)

omit [Etale ((BigFppfOver.toScheme B S hS).map ψ)] in
include hβ hsq₀ in
/-- The square formed by `c₀`, `thinBase`, `ι₀ ≫ β` and `ψ` commutes. -/
theorem thin_condition : c₀ ≫ thinBase B S hS φ x₀ = (ι₀ ≫ β) ≫ ψ := by
  apply yoneda.map_injective
  rw [thinBase, Functor.map_comp, Functor.map_preimage, ← Category.assoc, ← hsq₀.w,
    Category.assoc, hβ, ← Functor.map_comp, Category.assoc]

/-- The morphism of the site `W₀ ⟶ O₀ ×_Y Y'` whose invertibility is tested. -/
def thinComparison : W₀ ⟶ pullback (thinBase B S hS φ x₀) ψ :=
  pullback.lift c₀ (ι₀ ≫ β) (thin_condition B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀)

include hwe hX in
/-- If `x₀` is surjective and `thinComparison` is an isomorphism, then the morphism
`h_W ⟶ X ×_Y Y'` with components `w` and `β` is an isomorphism. -/
theorem isIso_lift_of_isIso_thin (hx₀ : IsSurjective B S hS x₀)
    (hiso : IsIso (thinComparison B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀)) :
    IsIso (pullback.lift w (yoneda.map β) (by rw [hβ, Functor.map_comp]) :
      yoneda.obj W ⟶ pullback φ (yoneda.map ψ)) := by
  set f : yoneda.obj W ⟶ pullback φ (yoneda.map ψ) :=
    pullback.lift w (yoneda.map β) (by rw [hβ, Functor.map_comp])
  have hf_fst : f ≫ pullback.fst φ (yoneda.map ψ) = w := pullback.lift_fst _ _ _
  have hf_snd : f ≫ pullback.snd φ (yoneda.map ψ) = yoneda.map β := pullback.lift_snd _ _ _
  have hY : IsAlgebraicSpace B S hS (yoneda.obj Y) := isAlgebraicSpace_yoneda B S hS Y
  have hY' : IsAlgebraicSpace B S hS (yoneda.obj Y') := isAlgebraicSpace_yoneda B S hS Y'
  have hA : IsAlgebraicSpace B S hS (pullback φ (yoneda.map ψ)) :=
    isAlgebraicSpace_pullback B S hS φ (yoneda.map ψ) hX hY' hY
  have hfst : IsEtale B S hS (pullback.fst φ (yoneda.map ψ)) := by
    have h := isEtale_pullback_snd_yoneda_map (t := ψ) inferInstance φ
    have he : pullback.fst φ (yoneda.map ψ) =
        (pullbackSymmetry φ (yoneda.map ψ)).hom ≫ pullback.snd (yoneda.map ψ) φ := by simp
    rw [he]
    exact isEtale_comp B S hS (isEtale_of_iso B S hS _) h
  have hfe : IsEtale B S hS f :=
    isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS W) hA hX f w _
      ((isEtale_iff_presheaf_of_yoneda B S hS w).2 hwe) hfst hf_fst
  set A₀ := pullback (thinBase B S hS φ x₀) ψ
  have hcond : (yoneda.map (pullback.fst (thinBase B S hS φ x₀) ψ) ≫ x₀) ≫ φ =
      yoneda.map (pullback.snd (thinBase B S hS φ x₀) ψ) ≫ yoneda.map ψ := by
    rw [Category.assoc, ← Functor.map_preimage yoneda (x₀ ≫ φ), ← Functor.map_comp,
      ← Functor.map_comp, ← thinBase, pullback.condition]
  set p : yoneda.obj A₀ ⟶ pullback φ (yoneda.map ψ) :=
    pullback.lift (yoneda.map (pullback.fst _ _) ≫ x₀) (yoneda.map (pullback.snd _ _)) hcond
  have hp_fst : p ≫ pullback.fst φ (yoneda.map ψ) =
      yoneda.map (pullback.fst (thinBase B S hS φ x₀) ψ) ≫ x₀ := pullback.lift_fst _ _ _
  have hp_snd : p ≫ pullback.snd φ (yoneda.map ψ) =
      yoneda.map (pullback.snd (thinBase B S hS φ x₀) ψ) := pullback.lift_snd _ _ _
  have hsqtop : IsPullback (yoneda.map (pullback.fst (thinBase B S hS φ x₀) ψ)) p x₀
      (pullback.fst φ (yoneda.map ψ)) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd φ (yoneda.map ψ)) (v₂₂ := φ)
      (h₃₁ := yoneda.map ψ) ?_ ?_ (IsPullback.of_hasPullback _ _)
    · have h := (IsPullback.of_hasPullback (thinBase B S hS φ x₀) ψ).map yoneda
      rw [hp_snd, show x₀ ≫ φ = yoneda.map (thinBase B S hS φ x₀) from
        (Functor.map_preimage yoneda _).symm]
      exact h
    · rw [hp_fst]
  have hA₀ : IsAlgebraicSpace B S hS (yoneda.obj A₀) := isAlgebraicSpace_yoneda B S hS A₀
  have hp : IsSurjective B S hS p := by
    let sq : IsPullback (P := (⟨_, hA₀⟩ : AlgebraicSpaces B S hS))
        (X := (⟨_, isAlgebraicSpace_yoneda B S hS O₀⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨_, hA⟩ : AlgebraicSpaces B S hS)) (Z := (⟨_, hX⟩ : AlgebraicSpaces B S hS))
        (ObjectProperty.homMk (yoneda.map (pullback.fst (thinBase B S hS φ x₀) ψ)))
        (ObjectProperty.homMk p) (ObjectProperty.homMk x₀)
        (ObjectProperty.homMk (pullback.fst φ (yoneda.map ψ))) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsqtop
    exact isSurjective_of_isPullback B S hS sq hx₀
  have hκ_fst : thinComparison B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀ ≫ pullback.fst _ _ = c₀ :=
    pullback.lift_fst _ _ _
  have hκ_snd : thinComparison B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀ ≫ pullback.snd _ _ = ι₀ ≫ β :=
    pullback.lift_snd _ _ _
  have hsq : IsPullback (yoneda.map (thinComparison B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀))
      (yoneda.map ι₀) p f := by
    refine IsPullback.of_right ?_ ?_ hsqtop
    · rw [← Functor.map_comp, hκ_fst, hf_fst]
      exact hsq₀.flip
    · apply pullback.hom_ext
      · rw [Category.assoc, hp_fst, Category.assoc, hf_fst, ← Functor.map_comp_assoc, hκ_fst,
          hsq₀.w]
      · rw [Category.assoc, hp_snd, Category.assoc, hf_snd, ← Functor.map_comp, hκ_snd,
          Functor.map_comp]
  have : IsIso (yoneda.map (thinComparison B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀)) := inferInstance
  exact isIso_of_isEtale_of_isIso_pullback_of_isSurjective B S hS hA hA₀
    (isAlgebraicSpace_yoneda B S hS W) hsq this hp hfe

include hwe hX in
/-- If `W` is affine, `x₀` is surjective and `thinComparison` is an isomorphism, then the
algebraic space `X ×_Y Y'` is affine. -/
theorem isAffineSpace_pullback_of_isIso_thin
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (hx₀ : IsSurjective B S hS x₀)
    (hiso : IsIso (thinComparison B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀)) :
    IsAffineSpace B S hS (pullback φ (yoneda.map ψ)) := by
  have := isIso_lift_of_isIso_thin B S hS hX w hwe φ ψ β hβ x₀ ι₀ c₀ hsq₀ hx₀ hiso
  exact (isAffineSpace_yoneda B S hS W inferInstance).of_iso (@asIso _ _ _ _ _ this)

end AlgebraicGeometry.Space

end
