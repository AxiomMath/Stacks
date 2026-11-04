module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusCompositionNatTrans

/-!
# The cohomology comparison of an exact functor is compatible with a composition

Let `U₁ : C₀ ⥤ C₁`, `U₂ : C₁ ⥤ C₂` and `U : C₀ ⥤ C₂` be exact additive functors of abelian
categories with derived categories, the sources of the first two having enough injectives, and
let `c : U₁ ⋙ U₂ ≅ U`. For an exact functor `F` the comparison
`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso` identifies `H^n ∘ RF` with `F ∘ H^n` on
the bounded below derived category. This file proves the cocycle identity those three
comparisons satisfy: the one for `U`, read through the comparison `RU₁ ⋙ RU₂ ≅ RU` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`, is the composite of the ones for
`U₁` and `U₂`, read through `c`.

## Main results

* `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso_comp_hom_app`: the cocycle identity at
  an object of the bounded below derived category.
* `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso_comp`: **the cocycle identity**, as an
  identity of natural transformations, in the form in which the comparisons enter a descent
  along a derived-functor unit — with every comparison inverted.

## Implementation notes

The comparison is the identification `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso` of
the right derived functor with the degreewise action, followed by the comparison
`Stacks.DerivedFunctor.derivedHomologyIso` of the degreewise action with cohomology. The first
half of the cocycle identity is therefore
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_compNatTrans`, which replaces the derived
comparison by the degreewise one, and the second half is the cocycle identity for
`derivedHomologyIso`: that is
`Stacks.DerivedFunctor.derivedHomologyIso_comp_hom_app_plus` for the comparison of the
degreewise actions and `Stacks.DerivedFunctor.derivedHomologyIso_naturality` for the degreewise
action of `c`. Nothing else enters, and in particular no object of the bounded below homotopy
category appears: both halves hold at every object of the bounded below derived category.

The rearrangement of the four squares into the identity is stated for morphisms in an abstract
category, because at the types at hand a `rw`-driven reassociation does not match: the two
spellings of a composite of functors on bounded below derived categories are equal only after
unfolding definitions that the derived category does not expose.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₀ v₁ v₂ u₀ u₁ u₂

namespace Stacks.DerivedFunctor

/-! ### The rearrangements, on variables -/

/-- Solving a factorization through two invertible morphisms for the inverses. -/
private theorem solve_inv {E : Type*} [Category* E] {o₁ o₂ o₃ o₄ o₅ : E}
    {A : o₁ ⟶ o₂} {A' : o₂ ⟶ o₁} {B : o₂ ⟶ o₃} {B' : o₃ ⟶ o₂} {X : o₃ ⟶ o₄}
    {G : o₁ ⟶ o₅} {H : o₅ ⟶ o₄} {H' : o₄ ⟶ o₅}
    (hA : A' ≫ A = 𝟙 o₂) (hB : B' ≫ B = 𝟙 o₃) (hH : H ≫ H' = 𝟙 o₅)
    (key : A ≫ B ≫ X = G ≫ H) : X ≫ H' = B' ≫ A' ≫ G :=
  calc X ≫ H' = (B' ≫ B) ≫ X ≫ H' := by rw [hB, Category.id_comp]
    _ = B' ≫ ((A' ≫ A) ≫ B ≫ X) ≫ H' := by simp [reassoc_of% hA]
    _ = B' ≫ A' ≫ (A ≫ B ≫ X) ≫ H' := by simp
    _ = B' ≫ A' ≫ (G ≫ H) ≫ H' := by rw [key]
    _ = B' ≫ A' ≫ G := by simp [hH]

/-- The rearrangement of the four squares of the cocycle identity for cohomology. -/
private theorem homology_chain {E : Type*} [Category* E]
    {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ : E}
    {cI : o₁ ⟶ o₂} {ΦU : o₂ ⟶ o₃} {dU : o₃ ⟶ o₄}
    {Φ₂ : o₁ ⟶ o₅} {m : o₅ ⟶ o₆} {dD : o₆ ⟶ o₃}
    {cdw : o₆ ⟶ o₇} {dcomp : o₇ ⟶ o₈} {ch : o₈ ⟶ o₄}
    {d₂' : o₆ ⟶ o₉} {Ud₁ : o₉ ⟶ o₈} {d₂ : o₅ ⟶ o₁₀} {UΦ₁ : o₁₀ ⟶ o₉}
    (h₁₂ : cI ≫ ΦU = Φ₂ ≫ m ≫ dD) (h₃ : dD ≫ dU = cdw ≫ dcomp ≫ ch)
    (h₄ : cdw ≫ dcomp = d₂' ≫ Ud₁) (h₅ : m ≫ d₂' = d₂ ≫ UΦ₁) :
    cI ≫ ΦU ≫ dU = (Φ₂ ≫ d₂) ≫ (UΦ₁ ≫ Ud₁) ≫ ch := by
  rw [← Category.assoc cI, h₁₂]
  simp only [Category.assoc]
  rw [h₃, reassoc_of% h₄, reassoc_of% h₅]

/-- Replacing the last two legs of a composite by an equal two-fold composite, and
reassociating. -/
private theorem split_comp {E : Type*} [Category* E] {o₁ o₂ o₃ o₄ o₅ : E}
    {a : o₁ ⟶ o₂} {b : o₂ ⟶ o₃} {d : o₃ ⟶ o₄} {p : o₂ ⟶ o₅} {q : o₅ ⟶ o₄}
    (h : b ≫ d = p ≫ q) : (a ≫ b) ≫ d = a ≫ p ≫ q := by
  rw [Category.assoc, h]

/-- The comparison `H^n ∘ RF ≅ F ∘ H^n` at an object, unfolded into its two factors. -/
private theorem exactRightDerivedPlusHomologyIso_hom_app_eq {A B : Type*} [Category* A]
    [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (n : ℤ) (K : DerivedCategory.Plus A) :
    (exactRightDerivedPlusHomologyIso F n).hom.app K =
      (DerivedCategory.Plus.homologyFunctor B n).map
          ((exactMapDerivedCategoryPlusIso F).inv.app K) ≫
        (derivedHomologyIso F n).hom.app (DerivedCategory.Plus.ι.obj K) := rfl

/-! ### The cocycle identity -/

section Comp

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [EnoughInjectives C₀] [EnoughInjectives C₁]
  (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (c : U₁ ⋙ U₂ ≅ U)

/-- **The cocycle identity for the cohomology comparison of an exact functor**, at an object of
the bounded below derived category: the comparison for `U`, preceded by the cohomology of the
derived comparison `RU₁ ⋙ RU₂ ≅ RU`, is the comparison for `U₂`, then `U₂` of the comparison for
`U₁`, then `c`. -/
theorem exactRightDerivedPlusHomologyIso_comp_hom_app (n : ℤ) (K : DerivedCategory.Plus C₀) :
    (DerivedCategory.Plus.homologyFunctor C₂ n).map
          ((Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).hom.app K) ≫
        (exactRightDerivedPlusHomologyIso U n).hom.app K =
      (exactRightDerivedPlusHomologyIso U₂ n).hom.app (U₁.rightDerivedFunctorPlus.obj K) ≫
        U₂.map ((exactRightDerivedPlusHomologyIso U₁ n).hom.app K) ≫
          c.hom.app ((DerivedCategory.Plus.homologyFunctor C₀ n).obj K) := by
  have hA : (exactMapDerivedCategoryPlusIso U₂).inv.app
        (U₁.mapDerivedCategoryPlus.obj K) ≫
      (exactMapDerivedCategoryPlusIso U₂).hom.app (U₁.mapDerivedCategoryPlus.obj K) = 𝟙 _ :=
    (exactMapDerivedCategoryPlusIso U₂).inv_hom_id_app _
  have hB : U₂.rightDerivedFunctorPlus.map ((exactMapDerivedCategoryPlusIso U₁).inv.app K) ≫
      U₂.rightDerivedFunctorPlus.map ((exactMapDerivedCategoryPlusIso U₁).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hcomb : (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).hom.app K ≫
        (exactMapDerivedCategoryPlusIso U).inv.app K =
      (exactMapDerivedCategoryPlusIso U₂).inv.app (U₁.rightDerivedFunctorPlus.obj K) ≫
        U₂.mapDerivedCategoryPlus.map ((exactMapDerivedCategoryPlusIso U₁).inv.app K) ≫
          (mapDerivedCategoryPlusCompNatTrans U₁ U₂ U c).app K := by
    rw [solve_inv hA hB ((exactMapDerivedCategoryPlusIso U).hom_inv_id_app K)
        (exactMapDerivedCategoryPlusIso_compNatTrans U₁ U₂ U c K), ← Category.assoc,
      (exactMapDerivedCategoryPlusIso U₂).inv.naturality
        ((exactMapDerivedCategoryPlusIso U₁).inv.app K), Category.assoc]
  have h₁₂ := congrArg (DerivedCategory.Plus.homologyFunctor C₂ n).map hcomb
  simp only [Functor.map_comp] at h₁₂
  have hnt : (DerivedCategory.Plus.homologyFunctor C₂ n).map
          ((mapDerivedCategoryPlusNatTrans c.hom).app K) ≫
        (derivedHomologyIso U n).hom.app (DerivedCategory.Plus.ι.obj K) =
      (derivedHomologyIso (U₁ ⋙ U₂) n).hom.app (DerivedCategory.Plus.ι.obj K) ≫
        c.hom.app ((DerivedCategory.Plus.homologyFunctor C₀ n).obj K) := by
    have h := congr_app (derivedHomologyIso_naturality c.hom n)
      (DerivedCategory.Plus.ι.obj K)
    rwa [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at h
  have h₃ : (DerivedCategory.Plus.homologyFunctor C₂ n).map
          ((mapDerivedCategoryPlusCompNatTrans U₁ U₂ U c).app K) ≫
        (derivedHomologyIso U n).hom.app (DerivedCategory.Plus.ι.obj K) =
      (DerivedCategory.Plus.homologyFunctor C₂ n).map
          ((mapDerivedCategoryPlusCompIso U₁ U₂).hom.app K) ≫
        (derivedHomologyIso (U₁ ⋙ U₂) n).hom.app (DerivedCategory.Plus.ι.obj K) ≫
          c.hom.app ((DerivedCategory.Plus.homologyFunctor C₀ n).obj K) := by
    rw [show (mapDerivedCategoryPlusCompNatTrans U₁ U₂ U c).app K =
        (mapDerivedCategoryPlusCompIso U₁ U₂).hom.app K ≫
          (mapDerivedCategoryPlusNatTrans c.hom).app K from rfl,
      (DerivedCategory.Plus.homologyFunctor C₂ n).map_comp]
    exact split_comp hnt
  have h₅ : (DerivedCategory.Plus.homologyFunctor C₂ n).map
          (U₂.mapDerivedCategoryPlus.map ((exactMapDerivedCategoryPlusIso U₁).inv.app K)) ≫
        (derivedHomologyIso U₂ n).hom.app
          (DerivedCategory.Plus.ι.obj (U₁.mapDerivedCategoryPlus.obj K)) =
      (derivedHomologyIso U₂ n).hom.app
          (DerivedCategory.Plus.ι.obj (U₁.rightDerivedFunctorPlus.obj K)) ≫
        U₂.map ((DerivedCategory.Plus.homologyFunctor C₁ n).map
          ((exactMapDerivedCategoryPlusIso U₁).inv.app K)) :=
    (derivedHomologyIso U₂ n).hom.naturality
      (DerivedCategory.Plus.ι.map ((exactMapDerivedCategoryPlusIso U₁).inv.app K))
  have hmap : U₂.map ((exactRightDerivedPlusHomologyIso U₁ n).hom.app K) =
      U₂.map ((DerivedCategory.Plus.homologyFunctor C₁ n).map
          ((exactMapDerivedCategoryPlusIso U₁).inv.app K)) ≫
        U₂.map ((derivedHomologyIso U₁ n).hom.app (DerivedCategory.Plus.ι.obj K)) := by
    rw [exactRightDerivedPlusHomologyIso_hom_app_eq U₁]
    exact U₂.map_comp _ _
  rw [exactRightDerivedPlusHomologyIso_hom_app_eq U,
    exactRightDerivedPlusHomologyIso_hom_app_eq U₂, hmap]
  exact homology_chain h₁₂ h₃ (derivedHomologyIso_comp_hom_app_plus U₁ U₂ n K).symm h₅

/-- **The cocycle identity for the cohomology comparison of an exact functor.** The comparison
`H^n ∘ RU ≅ U ∘ H^n` for `U`, read through the comparison `RU₁ ⋙ RU₂ ≅ RU` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`, is the composite of the
comparisons for `U₁` and for `U₂`, read through `c`. Every comparison is inverted, which is the
form a descent along a derived-functor unit consumes. -/
theorem exactRightDerivedPlusHomologyIso_comp (n : ℤ) :
    (exactRightDerivedPlusHomologyIso U n).inv ≫
        Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).inv
          (DerivedCategory.Plus.homologyFunctor C₂ n) =
      Functor.whiskerLeft (DerivedCategory.Plus.homologyFunctor C₀ n) c.inv ≫
        Functor.whiskerRight (exactRightDerivedPlusHomologyIso U₁ n).inv U₂ ≫
          Functor.whiskerLeft U₁.rightDerivedFunctorPlus
            (exactRightDerivedPlusHomologyIso U₂ n).inv := by
  have hPQ : Functor.isoWhiskerRight
          (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c)
          (DerivedCategory.Plus.homologyFunctor C₂ n) ≪≫
        exactRightDerivedPlusHomologyIso U n =
      Functor.isoWhiskerLeft U₁.rightDerivedFunctorPlus
            (exactRightDerivedPlusHomologyIso U₂ n) ≪≫
          Functor.isoWhiskerRight (exactRightDerivedPlusHomologyIso U₁ n) U₂ ≪≫
            Functor.isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor C₀ n) c := by
    ext K
    exact exactRightDerivedPlusHomologyIso_comp_hom_app U₁ U₂ U c n K
  simpa only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Category.assoc] using congrArg Iso.inv hPQ

end Comp

end Stacks.DerivedFunctor

end
