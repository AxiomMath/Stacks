module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinKeyFormula
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardPulledBackModule

/-!
# Stacks 0B73 for modules pulled back from other schemes, read through proper morphisms

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `V` be locally of
finite type over `S`, carrying two invertible modules `L₁ = q₁^* K₁` and `L₂ = q₂^* K₂` pulled
back along morphisms `q_i : V ⟶ P_i`, with pulled-back global sections `s_i = q_i^* t_i` and zero
schemes `Z_i = Z(s_i)`. Stacks 0B73 says that the two composites of Gysin maps
`A_{k+2}(V) ⟶ A_k(Z_1 ∩ Z_2)` agree.

In applications the intermediate zero schemes are often read on other schemes: `Z₁` through a
proper morphism `u₁ : Z₁ ⟶ Y₁`, on which the second module is the pullback of `K₂` along some
`r₂ : Y₁ ⟶ P₂` compatible with `u₁`, and symmetrically `Z₂` through `u₂ : Z₂ ⟶ Y₂` and
`r₁ : Y₂ ⟶ P₁`. This file states Stacks 0B73 in that form: pushing the Gysin image of `s₁` forward
to `Y₁` and applying the Gysin map of `r₂^* t₂` agrees, after a proper comparison morphism `w`
between the two zero schemes reached, with the composite in the other order. The comparison is
any `w` compatible with given maps of `Y₁` and `Y₂` back to `V`, the second of which is a
monomorphism on the zero scheme.

## Main results

* `Stacks.Chow.gysinSystemOfInvertible_comm_properPushforward`: Stacks 0B73 for modules pulled
  back from other schemes, read through proper morphisms.

## References

* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Stacks 0B73 for modules pulled back from other schemes, read through proper morphisms.** Let
`L₁ = q₁^* K₁` and `L₂ = q₂^* K₂` be invertible on `V` with sections `s_i = q_i^* t_i` and zero
schemes `Z_i`. Let `u₁ : Z₁ ⟶ Y₁` and `u₂ : Z₂ ⟶ Y₂` be proper, with `r₂ : Y₁ ⟶ P₂` and
`r₁ : Y₂ ⟶ P₁` compatible with them and with maps `y_i : Y_i ⟶ V` restricting to the inclusions of
`Z_i`. Then for every proper `w` from the zero scheme of `r₂^* t₂` to that of `r₁^* t₁` over `V`
and over the base, with the second zero scheme mapping to `V` by a monomorphism,
`w_* (r₂^* t₂)^* u₁_* s₁^* x = (r₁^* t₁)^* u₂_* s₂^* x`. -/
theorem gysinSystemOfInvertible_comm_properPushforward (C : ChowSituation.{u})
    {V Y₁ Y₂ P₁ P₂ : Scheme.{u}} (pV : V ⟶ C.S) [LocallyOfFiniteType pV] (pY₁ : Y₁ ⟶ C.S)
    [LocallyOfFiniteType pY₁] (pY₂ : Y₂ ⟶ C.S) [LocallyOfFiniteType pY₂]
    (q₁ : V ⟶ P₁) (q₂ : V ⟶ P₂) (K₁ : P₁.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P₁.sheaf.obj P₁.ringCatSheaf.property K₁]
    (K₂ : P₂.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P₂.sheaf.obj P₂.ringCatSheaf.property K₂]
    (t₁ : Γ(K₁, ⊤)) (t₂ : Γ(K₂, ⊤))
    (u₁ : (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback q₁).obj K₁)
      (AlgebraicGeometry.pullbackGlobalSections q₁ K₁ t₁)).subscheme ⟶ Y₁) [IsProper u₁]
    (hu₁ : u₁ ≫ pY₁ = (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback q₁).obj K₁)
      (AlgebraicGeometry.pullbackGlobalSections q₁ K₁ t₁)).subschemeι ≫ pV)
    (r₂ : Y₁ ⟶ P₂) (hr₂ : u₁ ≫ r₂ = (Stacks.Divisors.zeroScheme V
      ((Scheme.Modules.pullback q₁).obj K₁)
      (AlgebraicGeometry.pullbackGlobalSections q₁ K₁ t₁)).subschemeι ≫ q₂)
    (y₁ : Y₁ ⟶ V) (hy₁ : u₁ ≫ y₁ = (Stacks.Divisors.zeroScheme V
      ((Scheme.Modules.pullback q₁).obj K₁)
      (AlgebraicGeometry.pullbackGlobalSections q₁ K₁ t₁)).subschemeι)
    (u₂ : (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback q₂).obj K₂)
      (AlgebraicGeometry.pullbackGlobalSections q₂ K₂ t₂)).subscheme ⟶ Y₂) [IsProper u₂]
    (hu₂ : u₂ ≫ pY₂ = (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback q₂).obj K₂)
      (AlgebraicGeometry.pullbackGlobalSections q₂ K₂ t₂)).subschemeι ≫ pV)
    (r₁ : Y₂ ⟶ P₁) (hr₁ : u₂ ≫ r₁ = (Stacks.Divisors.zeroScheme V
      ((Scheme.Modules.pullback q₂).obj K₂)
      (AlgebraicGeometry.pullbackGlobalSections q₂ K₂ t₂)).subschemeι ≫ q₁)
    (y₂ : Y₂ ⟶ V) (hy₂ : u₂ ≫ y₂ = (Stacks.Divisors.zeroScheme V
      ((Scheme.Modules.pullback q₂).obj K₂)
      (AlgebraicGeometry.pullbackGlobalSections q₂ K₂ t₂)).subschemeι)
    (w : (Stacks.Divisors.zeroScheme Y₁ ((Scheme.Modules.pullback r₂).obj K₂)
        (AlgebraicGeometry.pullbackGlobalSections r₂ K₂ t₂)).subscheme ⟶
      (Stacks.Divisors.zeroScheme Y₂ ((Scheme.Modules.pullback r₁).obj K₁)
        (AlgebraicGeometry.pullbackGlobalSections r₁ K₁ t₁)).subscheme) [IsProper w]
    (hw : w ≫ ((Stacks.Divisors.zeroScheme Y₂ ((Scheme.Modules.pullback r₁).obj K₁)
        (AlgebraicGeometry.pullbackGlobalSections r₁ K₁ t₁)).subschemeι ≫ pY₂) =
      (Stacks.Divisors.zeroScheme Y₁ ((Scheme.Modules.pullback r₂).obj K₂)
        (AlgebraicGeometry.pullbackGlobalSections r₂ K₂ t₂)).subschemeι ≫ pY₁)
    [Mono ((Stacks.Divisors.zeroScheme Y₂ ((Scheme.Modules.pullback r₁).obj K₁)
        (AlgebraicGeometry.pullbackGlobalSections r₁ K₁ t₁)).subschemeι ≫ y₂)]
    (hwy : w ≫ (Stacks.Divisors.zeroScheme Y₂ ((Scheme.Modules.pullback r₁).obj K₁)
        (AlgebraicGeometry.pullbackGlobalSections r₁ K₁ t₁)).subschemeι ≫ y₂ =
      (Stacks.Divisors.zeroScheme Y₁ ((Scheme.Modules.pullback r₂).obj K₂)
        (AlgebraicGeometry.pullbackGlobalSections r₂ K₂ t₂)).subschemeι ≫ y₁)
    (k : ℤ) (x : chowGroup C pV (k + 1 + 1)) :
    properChowPushforward C _ _ w hw k (properPushforwardDescends C _ _ _ _ _)
        ((gysinSystemOfInvertible C).onChow pY₁ ((Scheme.Modules.pullback r₂).obj K₂)
          (AlgebraicGeometry.pullbackGlobalSections r₂ K₂ t₂) k
          (properChowPushforward C _ pY₁ u₁ hu₁ (k + 1) (properPushforwardDescends C _ _ _ _ _)
            ((gysinSystemOfInvertible C).onChow pV ((Scheme.Modules.pullback q₁).obj K₁)
              (AlgebraicGeometry.pullbackGlobalSections q₁ K₁ t₁) (k + 1) x))) =
      (gysinSystemOfInvertible C).onChow pY₂ ((Scheme.Modules.pullback r₁).obj K₁)
        (AlgebraicGeometry.pullbackGlobalSections r₁ K₁ t₁) k
        (properChowPushforward C _ pY₂ u₂ hu₂ (k + 1) (properPushforwardDescends C _ _ _ _ _)
          ((gysinSystemOfInvertible C).onChow pV ((Scheme.Modules.pullback q₂).obj K₂)
            (AlgebraicGeometry.pullbackGlobalSections q₂ K₂ t₂) (k + 1) x)) := by
  have := exists_isProper_zeroScheme_pullback_comp_hom
    (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback q₁).obj K₁)
      (AlgebraicGeometry.pullbackGlobalSections q₁ K₁ t₁)).subschemeι q₂ r₂ u₁ hr₂ K₂ t₂
  obtain ⟨j₁, hj₁⟩ := this
  have := hj₁.1
  have := exists_isProper_zeroScheme_pullback_comp_hom
    (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback q₂).obj K₂)
      (AlgebraicGeometry.pullbackGlobalSections q₂ K₂ t₂)).subschemeι q₁ r₁ u₂ hr₁ K₁ t₁
  obtain ⟨j₂, hj₂⟩ := this
  have := hj₂.1
  obtain ⟨e, he⟩ := exists_iso_zeroSchemeInter ((Scheme.Modules.pullback q₁).obj K₁)
    ((Scheme.Modules.pullback q₂).obj K₂) (AlgebraicGeometry.pullbackGlobalSections q₁ K₁ t₁)
    (AlgebraicGeometry.pullbackGlobalSections q₂ K₂ t₂)
  have hj₁b := ((reassoc_of% hj₁.2) pY₁).trans (congrArg (_ ≫ ·) hu₁)
  have hj₂b := ((reassoc_of% hj₂.2) pY₂).trans (congrArg (_ ≫ ·) hu₂)
  have h1 := gysinSystemOfInvertible_properPushforward_pullbackModule_comp C _ pY₁ _ q₂ r₂ u₁ hu₁
    hr₂ K₂ t₂ k j₁ hj₁.2 hj₁b
  have h2 := gysinSystemOfInvertible_properPushforward_pullbackModule_comp C _ pY₂ _ q₁ r₁ u₂ hu₂
    hr₁ K₁ t₁ k j₂ hj₂.2 hj₂b
  have hcomm := gysinChowOfInvertible_comm C pV k ((Scheme.Modules.pullback q₁).obj K₁)
    ((Scheme.Modules.pullback q₂).obj K₂) (AlgebraicGeometry.pullbackGlobalSections q₁ K₁ t₁)
    (AlgebraicGeometry.pullbackGlobalSections q₂ K₂ t₂) e he x
  have hmap : e.hom ≫ j₂ = j₁ ≫ w := by
    refine (cancel_mono ((Stacks.Divisors.zeroScheme Y₂ ((Scheme.Modules.pullback r₁).obj K₁)
      (AlgebraicGeometry.pullbackGlobalSections r₁ K₁ t₁)).subschemeι ≫ y₂)).1 ?_
    simp only [Category.assoc, hwy, reassoc_of% hj₁.2, reassoc_of% hj₂.2, hy₁, hy₂]
    exact he
  have hw' := (Category.assoc _ _ _).trans ((congrArg (j₁ ≫ ·) hw).trans hj₁b)
  refine ((congrArg (properChowPushforward C _ _ w hw k (properPushforwardDescends C _ _ _ _ _))
    (h1 _)).trans ?_).trans (h2 _).symm
  refine ((properChowPushforward_comp_apply C _ _ _ j₁ w (j₁ ≫ w) rfl hj₁b hw hw' k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _).symm.trans ?_)
  refine (properChowPushforward_comp_apply C _ _ _ e.hom j₂ (j₁ ≫ w) hmap
    (iso_zeroSchemeInter_comp_structureMorphism C pV _ _ _ _ e he) hj₂b hw' k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _).trans ?_
  exact congrArg _ hcomm

end Stacks.Chow

end
