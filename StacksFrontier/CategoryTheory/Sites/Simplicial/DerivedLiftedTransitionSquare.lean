module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedCompIsoCoherence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedCompIsoNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedLiftedTransitionLeg

/-!
# The derived image of a transition square

Let `Rn : T ⥤ A` and `Rm : T ⥤ B` be exact functors, `P : A ⥤ B` an exact functor and
`τ : Rn ⋙ P ⟶ Rm` a transition between them; let `Tf : T ⥤ T` be an exact endofunctor and let
`adj : Rn ⟶ Tf ⋙ Rn` and `chain : Rm ⟶ Tf ⋙ Rm` be transformations into its two whiskerings.
The square

  `P(adj_M) ≫ τ_{Tf M} = τ_M ≫ chain_M`

says that the transition carries `adj` to `chain`. This file carries that square to the derived
categories: `CategoryTheory.derivedNatTrans_square` is its derived image, and
`CategoryTheory.liftedTransition_square` restates it for a transition presented as a
`CategoryTheory.liftedTransition` along the localization of the homotopy category, which is the
form the derived transitions of Stacks 0D9P take.

## Main results

* `CategoryTheory.derivedNatTrans_square`: **the derived image of the square**, with both derived
  transitions spelled as `CategoryTheory.derivedNatTrans` of `τ` read through the compositor.
* `CategoryTheory.liftedTransition_square`: **the same square for a lifted transition**, stated
  for an abstract presentation `dT` of the derived transition of the kind
  `CategoryTheory.liftedTransition_eq_derivedNatTrans` supplies.

## Implementation notes

The two bracketings `(Tf ⋙ Rn) ⋙ P` and `Tf ⋙ (Rn ⋙ P)` of one functor are definitionally but
not syntactically equal, so the derived functors built over them are type-correct against one
another only at default transparency and a rewrite cannot move between them. The two
reassociations in the proofs are therefore stated as lemmas over the morphisms of an abstract
category.

## References

* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- In a category, given `c₁ ≫ c₁' = 𝟙`, `b₁' ≫ b₁ = 𝟙` and the four commutation relations
`hwr`, `hpent`, `hwl`, `hcomp`, the composites `a₁ ≫ a₂ ≫ b₁ ≫ b₂` and `c₁ ≫ c₂ ≫ c₃ ≫ c₄`
agree. -/
private theorem square_chain {Z : Type*} [Category Z]
    {o₀ o₁ o₂ p₀ p₁ p₂ q₀ q₁ q₂ : Z}
    (a₁ : o₀ ⟶ o₁) (a₂ : o₁ ⟶ o₂) (b₁ : o₂ ⟶ p₂) (b₂ : p₂ ⟶ q₂)
    (c₁ : o₀ ⟶ p₀) (c₁' : p₀ ⟶ o₀) (c₂ : p₀ ⟶ q₀) (c₃ : q₀ ⟶ q₁) (c₄ : q₁ ⟶ q₂)
    (w₁ : p₀ ⟶ p₁) (w₂ : p₁ ⟶ o₁) (pz : p₁ ⟶ p₂) (b₁' : p₂ ⟶ o₂) (v₁ : p₁ ⟶ q₁)
    (hc₁ : c₁ ≫ c₁' = 𝟙 o₀) (hb₁ : b₁' ≫ b₁ = 𝟙 p₂)
    (hwr : w₁ ≫ w₂ = c₁' ≫ a₁) (hpent : w₂ ≫ a₂ = pz ≫ b₁')
    (hwl : v₁ ≫ c₄ = pz ≫ b₂) (hcomp : w₁ ≫ v₁ = c₂ ≫ c₃) :
    a₁ ≫ a₂ ≫ b₁ ≫ b₂ = c₁ ≫ c₂ ≫ c₃ ≫ c₄ := by
  have step : c₁' ≫ a₁ ≫ a₂ ≫ b₁ ≫ b₂ = c₂ ≫ c₃ ≫ c₄ := by
    rw [← reassoc_of% hwr, reassoc_of% hpent, reassoc_of% hb₁, ← hwl, reassoc_of% hcomp]
  rw [← step, reassoc_of% hc₁]

/-- In a category, given `g ≫ e₁ = e₀ ≫ g'`, `g' = a₁ ≫ a₂` and
`a₁ ≫ a₂ ≫ b₁ ≫ b₂ = c₁ ≫ c₂ ≫ c₃ ≫ c₄`, the composites `g ≫ e₁ ≫ b₁ ≫ b₂` and
`(e₀ ≫ c₁ ≫ c₂) ≫ c₃ ≫ c₄` agree. -/
private theorem square_prefix {Z : Type*} [Category Z]
    {o₀ o₁ p₀ p₁ p₂ r₀ r₁ r₂ q₀ q₁ : Z}
    (g : o₀ ⟶ o₁) (e₁ : o₁ ⟶ p₁) (e₀ : o₀ ⟶ p₀) (g' : p₀ ⟶ p₁)
    (a₁ : p₀ ⟶ p₂) (a₂ : p₂ ⟶ p₁) (b₁ : p₁ ⟶ q₀) (b₂ : q₀ ⟶ q₁)
    (c₁ : p₀ ⟶ r₀) (c₂ : r₀ ⟶ r₁) (c₃ : r₁ ⟶ r₂) (c₄ : r₂ ⟶ q₁)
    (hnat : g ≫ e₁ = e₀ ≫ g') (hmap : g' = a₁ ≫ a₂)
    (hsq : a₁ ≫ a₂ ≫ b₁ ≫ b₂ = c₁ ≫ c₂ ≫ c₃ ≫ c₄) :
    g ≫ e₁ ≫ b₁ ≫ b₂ = (e₀ ≫ c₁ ≫ c₂) ≫ c₃ ≫ c₄ := by
  rw [reassoc_of% hnat, hmap]
  simp only [Category.assoc, hsq]

section Square

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₁ v₂ v₃ u₁ u₂ u₃ w₁ w₂ w₃

variable {T : Type u₁} {A : Type u₂} {B : Type u₃}
  [Category.{v₁} T] [Category.{v₂} A] [Category.{v₃} B]
  [Abelian T] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w₁} T] [HasDerivedCategory.{w₂} A] [HasDerivedCategory.{w₃} B]
  (Tf : T ⥤ T) (Rn : T ⥤ A) (Rm : T ⥤ B) (P : A ⥤ B)
  [Tf.Additive] [PreservesFiniteLimits Tf] [PreservesFiniteColimits Tf]
  [Rn.Additive] [PreservesFiniteLimits Rn] [PreservesFiniteColimits Rn]
  [Rm.Additive] [PreservesFiniteLimits Rm] [PreservesFiniteColimits Rm]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- **The derived image of a transition square.** Let `τ : Rn ⋙ P ⟶ Rm` be a transition of
exact functors, let `adj : Rn ⟶ Tf ⋙ Rn` and `chain : Rm ⟶ Tf ⋙ Rm`, and suppose that at every
object the transition carries `adj` to `chain`. Then the derived transformation of `adj`,
followed by the compositor and by the derived transition of `τ` at the derived functor of `Tf`,
is the derived transition of `τ` followed by the derived transformation of `chain` and the
compositor — the same square one level up.

Both derived transitions here are `CategoryTheory.derivedNatTrans` of `τ` conjugated by the
compositor of `Rn` with `P`. -/
theorem derivedNatTrans_square
    (adj : Rn ⟶ Tf ⋙ Rn) (τ : Rn ⋙ P ⟶ Rm) (chain : Rm ⟶ Tf ⋙ Rm)
    (hsq : ∀ M : T, P.map (adj.app M) ≫ τ.app (Tf.obj M) = τ.app M ≫ chain.app M)
    (K : DerivedCategory T) :
    P.mapDerivedCategory.map ((derivedNatTrans Rn (Tf ⋙ Rn) adj).app K) ≫
        P.mapDerivedCategory.map
            ((derivedCompIso Tf Rn (Tf ⋙ Rn) (Iso.refl _)).hom.app K) ≫
          (derivedCompIso Rn P (Rn ⋙ P) (Iso.refl _)).inv.app
              (Tf.mapDerivedCategory.obj K) ≫
            (derivedNatTrans (Rn ⋙ P) Rm τ).app (Tf.mapDerivedCategory.obj K) =
      (derivedCompIso Rn P (Rn ⋙ P) (Iso.refl _)).inv.app K ≫
        (derivedNatTrans (Rn ⋙ P) Rm τ).app K ≫
          (derivedNatTrans Rm (Tf ⋙ Rm) chain).app K ≫
            (derivedCompIso Tf Rm (Tf ⋙ Rm) (Iso.refl _)).hom.app K := by
  have hsqNT : Functor.whiskerRight adj P ≫ Functor.whiskerLeft Tf τ = τ ≫ chain :=
    NatTrans.ext (funext hsq)
  have hwr := congr_app (derivedCompIso_refl_hom_whiskerRight Rn (Tf ⋙ Rn) P adj) K
  have hwl := congr_app (derivedCompIso_refl_hom_whiskerLeft Tf (Rn ⋙ P) Rm τ) K
  have hpent := congr_app (derivedCompIso_pentagon Tf Rn P (Tf ⋙ Rn) (Rn ⋙ P)
    ((Tf ⋙ Rn) ⋙ P) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (fun Y => by simp)) K
  have hcomp := congr_app
    (((derivedNatTrans_comp (Rn ⋙ P) ((Tf ⋙ Rn) ⋙ P) (Tf ⋙ Rm)
            (Functor.whiskerRight adj P) (Functor.whiskerLeft Tf τ)).symm.trans
          (congrArg (derivedNatTrans (Rn ⋙ P) (Tf ⋙ Rm)) hsqNT)).trans
      (derivedNatTrans_comp (Rn ⋙ P) Rm (Tf ⋙ Rm) τ chain)) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hwr hwl hpent hcomp
  exact square_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) hwr hpent hwl hcomp

/-- **The derived image of a transition square, for a lifted transition.** The same square as
`CategoryTheory.derivedNatTrans_square`, stated for a transformation `dT` of the derived
functors presented as the derived transformation of `τ` read through an identification
`isoP : LP ≅ P.mapDerivedCategory` of the given functor of derived categories with the derived
functor of `P`, as in the conclusion of `CategoryTheory.liftedTransition_eq_derivedNatTrans`;
this is the form of the derived transitions of Stacks 0D9P. -/
theorem liftedTransition_square
    (adj : Rn ⟶ Tf ⋙ Rn) (τ : Rn ⋙ P ⟶ Rm) (chain : Rm ⟶ Tf ⋙ Rm)
    (hsq : ∀ M : T, P.map (adj.app M) ≫ τ.app (Tf.obj M) = τ.app M ≫ chain.app M)
    {LP : DerivedCategory A ⥤ DerivedCategory B} (isoP : LP ≅ P.mapDerivedCategory)
    (dT : Rn.mapDerivedCategory ⋙ LP ⟶ Rm.mapDerivedCategory)
    (hdT : dT = Functor.whiskerLeft Rn.mapDerivedCategory isoP.hom ≫
      (derivedCompIso Rn P (Rn ⋙ P) (Iso.refl _)).inv ≫ derivedNatTrans (Rn ⋙ P) Rm τ)
    (K : DerivedCategory T) :
    LP.map ((derivedNatTrans Rn (Tf ⋙ Rn) adj).app K ≫
          (derivedCompIso Tf Rn (Tf ⋙ Rn) (Iso.refl _)).hom.app K) ≫
        dT.app (Tf.mapDerivedCategory.obj K) =
      dT.app K ≫ (derivedNatTrans Rm (Tf ⋙ Rm) chain).app K ≫
        (derivedCompIso Tf Rm (Tf ⋙ Rm) (Iso.refl _)).hom.app K := by
  subst hdT
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  exact square_prefix _ _ _ _ _ _ _ _ _ _ _ _ (isoP.hom.naturality _)
    (P.mapDerivedCategory.map_comp _ _)
    (derivedNatTrans_square Tf Rn Rm P adj τ chain hsq K)

end Square

end CategoryTheory

end
