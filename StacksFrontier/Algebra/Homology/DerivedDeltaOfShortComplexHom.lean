module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact

/-!
# Naturality of the connecting morphism in the short complex of functors

Let `A` and `B` be abelian categories with enough injectives in `A`, and let

`F ⟶ G ⟶ H`,  `F' ⟶ G' ⟶ H'`

be two complexes of additive functors `A ⥤ B` which are short exact at every injective object of
`A`. Each of them has a long exact sequence of right derived functors, with connecting morphism
`CategoryTheory.rightDerivedDelta`. This file proves that a morphism of the two complexes --
natural transformations `α : F ⟶ F'`, `β : G ⟶ G'`, `γ : H ⟶ H'` with `i ≫ β = α ≫ i'` and
`q ≫ γ = β ≫ q'` -- induces a commuting square

`Rⁿ H ⟶ Rⁿ H' ⟶ Rⁿ⁺¹ F'  =  Rⁿ H ⟶ Rⁿ⁺¹ F ⟶ Rⁿ⁺¹ F'`

between the two connecting morphisms.

`CategoryTheory.InjectiveResolution.rightDerivedDelta_naturality` is the naturality of the
connecting morphism in the *object*; the statement here is the naturality in the *sequence*, which
is what compares the long exact sequences of two different short complexes of functors. The
Mayer--Vietoris sequence of a pair of opens covering an ambient open is built from such a short
complex of sections functors, and restricting the cover to a smaller ambient open is exactly a
morphism of short complexes, so this is what identifies the two Mayer--Vietoris connecting
morphisms.

## Main definitions

* `CategoryTheory.NatTrans.mapHomologicalComplexShortComplexHom`: the morphism of short complexes
  of homological complexes obtained by applying `α`, `β`, `γ` degreewise.

## Main results

* `CategoryTheory.InjectiveResolution.rightDerivedDelta_comp_of_hom`: the commuting square at one
  injective resolution.
* `CategoryTheory.rightDerivedDelta_comp_of_hom`: the commuting square of natural
  transformations.

## Implementation notes

Both connecting morphisms are computed from **the same** injective resolution `P` of the object,
so the comparison is the naturality of the snake-lemma connecting morphism of
`HomologicalComplex.HomologySequence.δ_naturality` for the morphism of short exact sequences of
complexes which `α`, `β`, `γ` induce on `P.cocomplex`. The identification of
`CategoryTheory.NatTrans.rightDerived` with the map on homology of the resolved complex is
`CategoryTheory.homologyMap_comp_isoRightDerivedObj'_inv`; it is used in the solved-for form
`Rⁿ γ = iso.hom ≫ homologyMap ≫ iso.inv`, so that the two isomorphisms cancel against the ones
inside `CategoryTheory.InjectiveResolution.rightDerivedDelta`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [Abelian A] [Abelian B] {F G H F' G' H' : A ⥤ B}

section Hom

variable [F.Additive] [G.Additive] [H.Additive] [F'.Additive] [G'.Additive] [H'.Additive]
  (i : F ⟶ G) (q : G ⟶ H) (hiq : i ≫ q = 0)
  (i' : F' ⟶ G') (q' : G' ⟶ H') (hiq' : i' ≫ q' = 0)
  (α : F ⟶ F') (β : G ⟶ G') (γ : H ⟶ H')
  (h₁ : i ≫ β = α ≫ i') (h₂ : q ≫ γ = β ≫ q')

include h₁ h₂

/-- **A morphism of complexes of functors, applied degreewise to a homological complex.** -/
def NatTrans.mapHomologicalComplexShortComplexHom {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex A c) :
    NatTrans.mapHomologicalComplexShortComplex i q hiq c K ⟶
      NatTrans.mapHomologicalComplexShortComplex i' q' hiq' c K where
  τ₁ := (NatTrans.mapHomologicalComplex α c).app K
  τ₂ := (NatTrans.mapHomologicalComplex β c).app K
  τ₃ := (NatTrans.mapHomologicalComplex γ c).app K
  comm₁₂ := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      ← NatTrans.mapHomologicalComplex_comp, h₁]
  comm₂₃ := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      ← NatTrans.mapHomologicalComplex_comp, h₂]

end Hom

section Derived

variable [HasInjectiveResolutions A]
  [F.Additive] [G.Additive] [H.Additive] [F'.Additive] [G'.Additive] [H'.Additive]
  (i : F ⟶ G) (q : G ⟶ H) (hiq : i ≫ q = 0)
  (hinj : ∀ X : A, Injective X → (NatTrans.appShortComplex i q hiq X).ShortExact)
  (i' : F' ⟶ G') (q' : G' ⟶ H') (hiq' : i' ≫ q' = 0)
  (hinj' : ∀ X : A, Injective X → (NatTrans.appShortComplex i' q' hiq' X).ShortExact)
  (α : F ⟶ F') (β : G ⟶ G') (γ : H ⟶ H')
  (h₁ : i ≫ β = α ≫ i') (h₂ : q ≫ γ = β ≫ q')

/-- The derived map of a natural transformation, read through the homology of a resolved
complex.  This is `CategoryTheory.homologyMap_comp_isoRightDerivedObj'_inv` solved for the
derived map. -/
theorem rightDerived_app_eq_conj (a : F ⟶ F') {X : A} (P : InjectiveResolution X) (n : ℕ) :
    (NatTrans.rightDerived a n).app X =
      (P.isoRightDerivedObj' F n).hom ≫
        HomologicalComplex.homologyMap
            ((NatTrans.mapHomologicalComplex a (ComplexShape.up ℕ)).app P.cocomplex) n ≫
          (P.isoRightDerivedObj' F' n).inv := by
  rw [homologyMap_comp_isoRightDerivedObj'_inv a P n, Iso.hom_inv_id_assoc]

include hinj hinj' h₁ h₂

/-- **The two connecting morphisms of a morphism of short complexes of functors agree**, at one
injective resolution.  Both are computed from the same resolution, so this is the naturality of
the snake-lemma connecting morphism for the induced morphism of short exact sequences of
complexes. -/
theorem InjectiveResolution.rightDerivedDelta_comp_of_hom {X : A} (P : InjectiveResolution X)
    (n : ℕ) :
    (NatTrans.rightDerived γ n).app X ≫
        InjectiveResolution.rightDerivedDelta i' q' hiq' hinj' P n =
      InjectiveResolution.rightDerivedDelta i q hiq hinj P n ≫
        (NatTrans.rightDerived α (n + 1)).app X := by
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    (NatTrans.mapHomologicalComplexShortComplexHom i q hiq i' q' hiq' α β γ h₁ h₂
      (ComplexShape.up ℕ) P.cocomplex)
    (InjectiveResolution.shortExact_map i q hiq hinj P)
    (InjectiveResolution.shortExact_map i' q' hiq' hinj' P) n (n + 1)
    (ComplexShape.up_rel_succ n)
  dsimp only [NatTrans.mapHomologicalComplexShortComplexHom] at hnat
  dsimp only [InjectiveResolution.rightDerivedDelta]
  rw [rightDerived_app_eq_conj γ P n, rightDerived_app_eq_conj α P (n + 1)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hnat]

/-- **The two connecting morphisms of a morphism of short complexes of functors agree.**  A
morphism `(α, β, γ)` from `F ⟶ G ⟶ H` to `F' ⟶ G' ⟶ H'` makes the square

`Rⁿ H ⟶ Rⁿ H' ⟶ Rⁿ⁺¹ F'`,  `Rⁿ H ⟶ Rⁿ⁺¹ F ⟶ Rⁿ⁺¹ F'`

of connecting morphisms commute. -/
theorem rightDerivedDelta_comp_of_hom (n : ℕ) :
    NatTrans.rightDerived γ n ≫ rightDerivedDelta i' q' hiq' hinj' n =
      rightDerivedDelta i q hiq hinj n ≫ NatTrans.rightDerived α (n + 1) := by
  ext X
  exact InjectiveResolution.rightDerivedDelta_comp_of_hom i q hiq hinj i' q' hiq' hinj' α β γ
    h₁ h₂ (injectiveResolution X) n

end Derived

end CategoryTheory

end
