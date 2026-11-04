module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons

/-!
# A coherence square for right derived functors on `D⁺`

Let `𝒜`, `ℬ`, `𝒞`, `𝒟`, `ℰ` be abelian categories with derived categories, the first four with
enough injectives, and let `a : 𝒜 ⥤ ℬ`, `b : ℬ ⥤ 𝒟`, `c : 𝒜 ⥤ 𝒞`, `d : 𝒞 ⥤ 𝒟`, `g : 𝒟 ⥤ ℰ` be
additive functors forming a square `a ⋙ b ≅ c ⋙ d` followed by `g`, together with three more
additive functors `p : 𝒜 ⥤ ℰ`, `q : ℬ ⥤ ℰ`, `r : 𝒞 ⥤ ℰ` and isomorphisms

`sq : a ⋙ b ≅ c ⋙ d`, `ea : a ⋙ q ≅ p`, `eb : b ⋙ g ≅ q`, `ec : c ⋙ r ≅ p`,
`ed : d ⋙ g ≅ r`

identifying the two factorizations of `p` through the square.  Assume `a`, `b`, `c`, `d` carry
injective objects to injective objects, so that
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` applies to each of the six composites
`a ⋙ q`, `b ⋙ g`, `c ⋙ r`, `d ⋙ g`, `a ⋙ b` and `c ⋙ d`.  Writing `RF` for
`CategoryTheory.Functor.rightDerivedFunctorPlus`, each of the five isomorphisms above produces a
comparison of right derived functors on bounded below derived categories, and this file proves
that the resulting square of comparisons commutes as soon as the *underived* one does: the two
ways of computing `Rp`, through `Ra ⋙ Rq ⟶ Ra ⋙ Rb ⋙ Rg` and through `Rc ⋙ Rr ⟶ Rc ⋙ Rd ⋙ Rg`,
agree.

## Main definitions

* `Stacks.DerivedFunctor.LeraySquare.derivedLeft`, `derivedLeftTail`, `derivedRight`,
  `derivedRightTail`: the four derived comparisons `Rp ≅ Ra ⋙ Rq`, `Rq ≅ Rb ⋙ Rg`,
  `Rp ≅ Rc ⋙ Rr`, `Rr ≅ Rd ⋙ Rg`.
* `Stacks.DerivedFunctor.LeraySquare.derivedSquare`: the derived comparison
  `Ra ⋙ Rb ≅ Rc ⋙ Rd` of the square itself.

## Main results

* `Stacks.DerivedFunctor.LeraySquare.derived_coherence`: **the derived square commutes** as soon
  as the underived one does.
* `Stacks.DerivedFunctor.LeraySquare.coherence_iff_natTrans`: the underived hypothesis, stated
  objectwise and as an identity of natural transformations; the two are interchangeable.

## References

* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M), when the composition comparison
  is an isomorphism
* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2), the comparison transformation
-/

@[expose] public noncomputable section

universe w₁ w₂ w₃ w₄ w₅ v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

open CategoryTheory CategoryTheory.Functor Limits

namespace Stacks.DerivedFunctor.LeraySquare

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Reading the comparisons on bounded below homotopy categories -/

section Degreewise

variable {X : Type u₁} {Y : Type u₂} {Z : Type u₄}
  [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₄} Z]
  [Abelian X] [Abelian Y] [Abelian Z]

/-- The action of an isomorphism of additive functors on bounded below homotopy categories,
read in the ambient homotopy category: the inverse half. -/
private lemma mapHomotopyCategoryPlusNatIso_inv_app_hom (F G : X ⥤ Y) [F.Additive] [G.Additive]
    (e : F ≅ G) (K : HomotopyCategory.Plus X) :
    ((mapHomotopyCategoryPlusNatIso e).inv.app K).hom =
      (NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app K.obj := rfl

/-- The action of an isomorphism of additive functors on bounded below homotopy categories,
read in the ambient homotopy category: the forward half. -/
private lemma mapHomotopyCategoryPlusNatIso_hom_app_hom (F G : X ⥤ Y) [F.Additive] [G.Additive]
    (e : F ≅ G) (K : HomotopyCategory.Plus X) :
    ((mapHomotopyCategoryPlusNatIso e).hom.app K).hom =
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K.obj := rfl

/-- The coherence isomorphism for a composite on bounded below homotopy categories, read in the
ambient homotopy category: the inverse half. -/
private lemma mapHomotopyCategoryPlusCompIso_inv_app_hom (F : X ⥤ Y) (G : Y ⥤ Z) (H : X ⥤ Z)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus X) :
    ((mapHomotopyCategoryPlusCompIso e).inv.app K).hom =
      (mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app K.obj := rfl

/-- The coherence isomorphism for a composite on bounded below homotopy categories, read in the
ambient homotopy category: the forward half. -/
private lemma mapHomotopyCategoryPlusCompIso_hom_app_hom (F : X ⥤ Y) (G : Y ⥤ Z) (H : X ⥤ Z)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus X) :
    ((mapHomotopyCategoryPlusCompIso e).hom.app K).hom =
      (mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K.obj := rfl

/-- The functor induced on bounded below homotopy categories acts on a morphism through its
underlying morphism of the ambient homotopy category. -/
private lemma mapHomotopyCategoryPlus_map_hom (G : Y ⥤ Z) [G.Additive]
    {K L : HomotopyCategory.Plus Y} (φ : K ⟶ L) :
    (G.mapHomotopyCategoryPlus.map φ).hom =
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map φ.hom := rfl

/-- The coherence isomorphism for a composite on homotopy categories is the image of the
coherence isomorphism on complexes: the inverse half. -/
private lemma mapHomotopyCategoryCompIso_inv_app (F : X ⥤ Y) (G : Y ⥤ Z) (H : X ⥤ Z)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (M : HomotopyCategory X (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app M =
      (HomotopyCategory.quotient Z (ComplexShape.up ℤ)).map
        ((mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app M.as) := rfl

/-- The forward half of `mapHomotopyCategoryCompIso_inv_app`. -/
private lemma mapHomotopyCategoryCompIso_hom_app (F : X ⥤ Y) (G : Y ⥤ Z) (H : X ⥤ Z)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (M : HomotopyCategory X (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app M =
      (HomotopyCategory.quotient Z (ComplexShape.up ℤ)).map
        ((mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app M.as) := rfl

/-- The complex underlying the image of a bounded below complex by an induced functor. -/
private lemma mapHomotopyCategoryPlus_obj_obj_as (F : X ⥤ Y) [F.Additive]
    (K : HomotopyCategory.Plus X) :
    (F.mapHomotopyCategoryPlus.obj K).obj.as =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj.as := rfl

end Degreewise

/-! ### Generic factorizations of the derived comparisons -/

section Generic

variable {X : Type u₁} {Y : Type u₂} {Y' : Type u₃} {Z : Type u₄}
  [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₃} Y'] [Category.{v₄} Z]
  [Abelian X] [Abelian Y] [Abelian Y'] [Abelian Z]
  [HasDerivedCategory.{w₁} X] [HasDerivedCategory.{w₂} Y] [HasDerivedCategory.{w₃} Y']
  [HasDerivedCategory.{w₄} Z]
  [EnoughInjectives X] [EnoughInjectives Y] [EnoughInjectives Y']

/-- **The factorization characterising a derived comparison `RH ≅ RF ⋙ RG`** attached to an
isomorphism `e : F ⋙ G ≅ H` with `F` preserving injective objects: composed with the
derived-functor unit of `RH` at a bounded below complex `K`, it is the degreewise action of
`e.inv`, the coherence isomorphism for the composite, and then the units of `RG` and of `RF`. -/
private lemma unit_comp_comparison_hom (F : X ⥤ Y) (G : Y ⥤ Z) (H : X ⥤ Z)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesInjectiveObjects]
    (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus X) :
    H.rightDerivedFunctorPlusUnit.app K ≫
        ((rightDerivedFunctorPlusNatIso e).symm ≪≫
          rightDerivedFunctorPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).inv.app K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K) ≫
        G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K) ≫
          G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  have h1 : H.rightDerivedFunctorPlusUnit.app K ≫
      (rightDerivedFunctorPlusNatIso e).inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).inv.app K) ≫
        (F ⋙ G).rightDerivedFunctorPlusUnit.app K := by
    rw [rightDerivedFunctorPlusNatIso, rightDerivedNatIso_inv]
    exact rightDerivedNatTrans_app _ _ _ _ _ _ K
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Category.assoc, h1, Category.assoc, rightDerivedFunctorPlusCompIso_hom,
    rightDerivedFunctorPlusComp_fac_app]

/-- **The factorization characterising the derived comparison of a square**
`s : F ⋙ G ≅ F' ⋙ G'` with `F` and `F'` preserving injective objects: composed with the units of
`RG` and of `RF` at a bounded below complex `K`, it is the degreewise action of `s.hom`, read
through the two coherence isomorphisms, followed by the units of `RG'` and of `RF'`. -/
private lemma unit_comp_square_hom (F : X ⥤ Y) (G : Y ⥤ Z) (F' : X ⥤ Y') (G' : Y' ⥤ Z)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [F.PreservesInjectiveObjects] [F'.PreservesInjectiveObjects]
    (s : F ⋙ G ≅ F' ⋙ G') (K : HomotopyCategory.Plus X) :
    G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) ≫
          ((rightDerivedFunctorPlusCompIso F G).symm ≪≫ rightDerivedFunctorPlusNatIso s ≪≫
            rightDerivedFunctorPlusCompIso F' G').hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso s).hom.app K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (F' ⋙ G'))).inv.app K) ≫
        G'.rightDerivedFunctorPlusUnit.app (F'.mapHomotopyCategoryPlus.obj K) ≫
          G'.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnit.app K) := by
  have h0 : G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K) ≫
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) ≫
        (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
          (rightDerivedFunctorPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) := by
    rw [rightDerivedFunctorPlusCompIso_hom, rightDerivedFunctorPlusComp_fac_app,
      ← Category.assoc, ← DerivedCategory.Plus.Qh.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have h1 : (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
      (rightDerivedFunctorPlusNatIso s).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso s).hom.app K) ≫
        (F' ⋙ G').rightDerivedFunctorPlusUnit.app K := by
    rw [rightDerivedFunctorPlusNatIso, rightDerivedNatIso_hom]
    exact rightDerivedNatTrans_app _ _ _ _ _ _ K
  have h2 : (F' ⋙ G').rightDerivedFunctorPlusUnit.app K ≫
      (rightDerivedFunctorPlusCompIso F' G').hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (F' ⋙ G'))).inv.app K) ≫
        G'.rightDerivedFunctorPlusUnit.app (F'.mapHomotopyCategoryPlus.obj K) ≫
          G'.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnit.app K) := by
    rw [rightDerivedFunctorPlusCompIso_hom, rightDerivedFunctorPlusComp_fac_app]
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Category.assoc (G.rightDerivedFunctorPlusUnit.app _), h0]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h1, h2]

/-- Naturality of the derived-functor unit: the unit followed by `RG` of the image of a morphism
is the image of the morphism followed by the unit. -/
private lemma unit_naturality (G : Y ⥤ Z) [G.Additive]
    {M N : HomotopyCategory.Plus Y} (ψ : M ⟶ N) :
    G.rightDerivedFunctorPlusUnit.app M ≫
        G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map ψ) =
      DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map ψ) ≫
        G.rightDerivedFunctorPlusUnit.app N :=
  (G.rightDerivedFunctorPlusUnit.naturality ψ).symm

end Generic

/-! ### The square -/

section Square

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D] [Category.{v₅} E]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [HasDerivedCategory.{w₄} D] [HasDerivedCategory.{w₅} E]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [EnoughInjectives D]
  {a : A ⥤ B} {b : B ⥤ D} {c : A ⥤ C} {d : C ⥤ D} {g : D ⥤ E}
  {p : A ⥤ E} {q : B ⥤ E} {r : C ⥤ E}
  [a.Additive] [b.Additive] [c.Additive] [d.Additive] [g.Additive]
  [p.Additive] [q.Additive] [r.Additive]
  [a.PreservesInjectiveObjects] [b.PreservesInjectiveObjects]
  [c.PreservesInjectiveObjects] [d.PreservesInjectiveObjects]

/-- **The derived comparison `Rp ≅ Ra ⋙ Rq`** attached to `ea : a ⋙ q ≅ p`: the invariance of
right derivation under isomorphism of functors, followed by the composition comparison for
`a ⋙ q`. -/
def derivedLeft (ea : a ⋙ q ≅ p) :
    p.rightDerivedFunctorPlus ≅ a.rightDerivedFunctorPlus ⋙ q.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusNatIso ea).symm ≪≫ rightDerivedFunctorPlusCompIso a q

/-- **The derived comparison `Rq ≅ Rb ⋙ Rg`** attached to `eb : b ⋙ g ≅ q`. -/
def derivedLeftTail (eb : b ⋙ g ≅ q) :
    q.rightDerivedFunctorPlus ≅ b.rightDerivedFunctorPlus ⋙ g.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusNatIso eb).symm ≪≫ rightDerivedFunctorPlusCompIso b g

/-- **The derived comparison `Rp ≅ Rc ⋙ Rr`** attached to `ec : c ⋙ r ≅ p`. -/
def derivedRight (ec : c ⋙ r ≅ p) :
    p.rightDerivedFunctorPlus ≅ c.rightDerivedFunctorPlus ⋙ r.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusNatIso ec).symm ≪≫ rightDerivedFunctorPlusCompIso c r

/-- **The derived comparison `Rr ≅ Rd ⋙ Rg`** attached to `ed : d ⋙ g ≅ r`. -/
def derivedRightTail (ed : d ⋙ g ≅ r) :
    r.rightDerivedFunctorPlus ≅ d.rightDerivedFunctorPlus ⋙ g.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusNatIso ed).symm ≪≫ rightDerivedFunctorPlusCompIso d g

/-- **The derived comparison `Ra ⋙ Rb ≅ Rc ⋙ Rd` of the square** attached to
`sq : a ⋙ b ≅ c ⋙ d`: the composition comparison for `a ⋙ b` inverted, the invariance
comparison for `sq`, and the composition comparison for `c ⋙ d`. -/
def derivedSquare (sq : a ⋙ b ≅ c ⋙ d) :
    a.rightDerivedFunctorPlus ⋙ b.rightDerivedFunctorPlus ≅
      c.rightDerivedFunctorPlus ⋙ d.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusCompIso a b).symm ≪≫ rightDerivedFunctorPlusNatIso sq ≪≫
    rightDerivedFunctorPlusCompIso c d

/-- The characterising factorization of `Stacks.DerivedFunctor.LeraySquare.derivedLeft`. -/
private lemma unit_comp_derivedLeft (ea : a ⋙ q ≅ p) (K : HomotopyCategory.Plus A) :
    p.rightDerivedFunctorPlusUnit.app K ≫
        (derivedLeft ea).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso ea).inv.app K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (a ⋙ q))).inv.app K) ≫
        q.rightDerivedFunctorPlusUnit.app (a.mapHomotopyCategoryPlus.obj K) ≫
          q.rightDerivedFunctorPlus.map (a.rightDerivedFunctorPlusUnit.app K) :=
  unit_comp_comparison_hom a q p ea K

/-- The characterising factorization of `Stacks.DerivedFunctor.LeraySquare.derivedLeftTail`. -/
private lemma unit_comp_derivedLeftTail (eb : b ⋙ g ≅ q) (K : HomotopyCategory.Plus B) :
    q.rightDerivedFunctorPlusUnit.app K ≫
        (derivedLeftTail eb).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso eb).inv.app K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (b ⋙ g))).inv.app K) ≫
        g.rightDerivedFunctorPlusUnit.app (b.mapHomotopyCategoryPlus.obj K) ≫
          g.rightDerivedFunctorPlus.map (b.rightDerivedFunctorPlusUnit.app K) :=
  unit_comp_comparison_hom b g q eb K

/-- The characterising factorization of `Stacks.DerivedFunctor.LeraySquare.derivedRight`. -/
private lemma unit_comp_derivedRight (ec : c ⋙ r ≅ p) (K : HomotopyCategory.Plus A) :
    p.rightDerivedFunctorPlusUnit.app K ≫
        (derivedRight ec).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso ec).inv.app K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (c ⋙ r))).inv.app K) ≫
        r.rightDerivedFunctorPlusUnit.app (c.mapHomotopyCategoryPlus.obj K) ≫
          r.rightDerivedFunctorPlus.map (c.rightDerivedFunctorPlusUnit.app K) :=
  unit_comp_comparison_hom c r p ec K

/-- The characterising factorization of `Stacks.DerivedFunctor.LeraySquare.derivedRightTail`. -/
private lemma unit_comp_derivedRightTail (ed : d ⋙ g ≅ r) (K : HomotopyCategory.Plus C) :
    r.rightDerivedFunctorPlusUnit.app K ≫
        (derivedRightTail ed).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso ed).inv.app K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (d ⋙ g))).inv.app K) ≫
        g.rightDerivedFunctorPlusUnit.app (d.mapHomotopyCategoryPlus.obj K) ≫
          g.rightDerivedFunctorPlus.map (d.rightDerivedFunctorPlusUnit.app K) :=
  unit_comp_comparison_hom d g r ed K

omit [EnoughInjectives D] [b.PreservesInjectiveObjects] [d.PreservesInjectiveObjects] in
/-- The characterising factorization of `Stacks.DerivedFunctor.LeraySquare.derivedSquare`. -/
private lemma unit_comp_derivedSquare (sq : a ⋙ b ≅ c ⋙ d) (K : HomotopyCategory.Plus A) :
    b.rightDerivedFunctorPlusUnit.app (a.mapHomotopyCategoryPlus.obj K) ≫
        b.rightDerivedFunctorPlus.map (a.rightDerivedFunctorPlusUnit.app K) ≫
          (derivedSquare sq).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (a ⋙ b))).hom.app K) ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso sq).hom.app K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (c ⋙ d))).inv.app K) ≫
        d.rightDerivedFunctorPlusUnit.app (c.mapHomotopyCategoryPlus.obj K) ≫
          d.rightDerivedFunctorPlus.map (c.rightDerivedFunctorPlusUnit.app K) :=
  unit_comp_square_hom a b c d sq K

omit [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  [EnoughInjectives D] [a.Additive] [b.Additive] [c.Additive] [d.Additive] [g.Additive]
  [p.Additive] [q.Additive] [r.Additive] [a.PreservesInjectiveObjects]
  [b.PreservesInjectiveObjects] [c.PreservesInjectiveObjects] [d.PreservesInjectiveObjects] in
/-- **The underived coherence hypothesis, objectwise and as an identity of natural
transformations** are equivalent. -/
theorem coherence_iff_natTrans (sq : a ⋙ b ≅ c ⋙ d) (ea : a ⋙ q ≅ p) (eb : b ⋙ g ≅ q)
    (ec : c ⋙ r ≅ p) (ed : d ⋙ g ≅ r) :
    (∀ X : A, eb.hom.app (a.obj X) ≫ ea.hom.app X =
        g.map (sq.hom.app X) ≫ ed.hom.app (c.obj X) ≫ ec.hom.app X) ↔
      Functor.whiskerLeft a eb.hom ≫ ea.hom =
        Functor.whiskerRight sq.hom g ≫ Functor.whiskerLeft c ed.hom ≫ ec.hom :=
  ⟨fun h ↦ NatTrans.ext (funext h), fun h X ↦ NatTrans.congr_app h X⟩

omit [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  [EnoughInjectives D] [a.Additive] [b.Additive] [c.Additive] [d.Additive] [g.Additive]
  [p.Additive] [q.Additive] [r.Additive] [a.PreservesInjectiveObjects]
  [b.PreservesInjectiveObjects] [c.PreservesInjectiveObjects] [d.PreservesInjectiveObjects] in
/-- The underived coherence hypothesis solved for the inverses. -/
private lemma underived_inv (sq : a ⋙ b ≅ c ⋙ d) (ea : a ⋙ q ≅ p) (eb : b ⋙ g ≅ q)
    (ec : c ⋙ r ≅ p) (ed : d ⋙ g ≅ r)
    (hcoh : ∀ X : A, eb.hom.app (a.obj X) ≫ ea.hom.app X =
      g.map (sq.hom.app X) ≫ ed.hom.app (c.obj X) ≫ ec.hom.app X) (X : A) :
    ea.inv.app X ≫ eb.inv.app (a.obj X) ≫ g.map (sq.hom.app X) =
      ec.inv.app X ≫ ed.inv.app (c.obj X) := by
  have h : g.map (sq.hom.app X) =
      eb.hom.app (a.obj X) ≫ ea.hom.app X ≫ ec.inv.app X ≫ ed.inv.app (c.obj X) := by
    rw [reassoc_of% (hcoh X)]
    simp
  rw [h]
  simp

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  [EnoughInjectives D] [a.PreservesInjectiveObjects] [b.PreservesInjectiveObjects]
  [c.PreservesInjectiveObjects] [d.PreservesInjectiveObjects] in
/-- **The coherence identity on complexes.**  The two routes through the square, applied
degreewise to a cochain complex of `𝒜`, agree. -/
private lemma coherence_complex (sq : a ⋙ b ≅ c ⋙ d) (ea : a ⋙ q ≅ p) (eb : b ⋙ g ≅ q)
    (ec : c ⋙ r ≅ p) (ed : d ⋙ g ≅ r)
    (hcoh : ∀ X : A, eb.hom.app (a.obj X) ≫ ea.hom.app X =
      g.map (sq.hom.app X) ≫ ed.hom.app (c.obj X) ≫ ec.hom.app X)
    (L : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex ea.inv (ComplexShape.up ℤ)).app L ≫
        (mapHomologicalComplexCompIso (Iso.refl (a ⋙ q)) (ComplexShape.up ℤ)).inv.app L ≫
        (NatTrans.mapHomologicalComplex eb.inv (ComplexShape.up ℤ)).app
            ((a.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        (mapHomologicalComplexCompIso (Iso.refl (b ⋙ g)) (ComplexShape.up ℤ)).inv.app
            ((a.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        (g.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((mapHomologicalComplexCompIso (Iso.refl (a ⋙ b)) (ComplexShape.up ℤ)).hom.app L ≫
            (NatTrans.mapHomologicalComplex sq.hom (ComplexShape.up ℤ)).app L ≫
            (mapHomologicalComplexCompIso (Iso.refl (c ⋙ d)) (ComplexShape.up ℤ)).inv.app L) =
      (NatTrans.mapHomologicalComplex ec.inv (ComplexShape.up ℤ)).app L ≫
        (mapHomologicalComplexCompIso (Iso.refl (c ⋙ r)) (ComplexShape.up ℤ)).inv.app L ≫
        (NatTrans.mapHomologicalComplex ed.inv (ComplexShape.up ℤ)).app
            ((c.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        (mapHomologicalComplexCompIso (Iso.refl (d ⋙ g)) (ComplexShape.up ℤ)).inv.app
            ((c.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, CategoryTheory.Functor.comp_obj,
    Category.id_comp, Category.comp_id]
  exact underived_inv sq ea eb ec ed hcoh (L.X n)

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  [EnoughInjectives D] [a.PreservesInjectiveObjects] [b.PreservesInjectiveObjects]
  [c.PreservesInjectiveObjects] [d.PreservesInjectiveObjects] in
/-- **The coherence identity on bounded below homotopy categories**: the two routes through the
square, applied to a bounded below complex of `𝒜` in the homotopy category, agree. -/
private lemma coherence_homotopy (sq : a ⋙ b ≅ c ⋙ d) (ea : a ⋙ q ≅ p) (eb : b ⋙ g ≅ q)
    (ec : c ⋙ r ≅ p) (ed : d ⋙ g ≅ r)
    (hcoh : ∀ X : A, eb.hom.app (a.obj X) ≫ ea.hom.app X =
      g.map (sq.hom.app X) ≫ ed.hom.app (c.obj X) ≫ ec.hom.app X)
    (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusNatIso ea).inv.app K ≫
        (mapHomotopyCategoryPlusCompIso (Iso.refl (a ⋙ q))).inv.app K ≫
        (mapHomotopyCategoryPlusNatIso eb).inv.app (a.mapHomotopyCategoryPlus.obj K) ≫
        (mapHomotopyCategoryPlusCompIso (Iso.refl (b ⋙ g))).inv.app
          (a.mapHomotopyCategoryPlus.obj K) ≫
        g.mapHomotopyCategoryPlus.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (a ⋙ b))).hom.app K ≫
            (mapHomotopyCategoryPlusNatIso sq).hom.app K ≫
            (mapHomotopyCategoryPlusCompIso (Iso.refl (c ⋙ d))).inv.app K) =
      (mapHomotopyCategoryPlusNatIso ec).inv.app K ≫
        (mapHomotopyCategoryPlusCompIso (Iso.refl (c ⋙ r))).inv.app K ≫
        (mapHomotopyCategoryPlusNatIso ed).inv.app (c.mapHomotopyCategoryPlus.obj K) ≫
        (mapHomotopyCategoryPlusCompIso (Iso.refl (d ⋙ g))).inv.app
          (c.mapHomotopyCategoryPlus.obj K) := by
  ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    mapHomotopyCategoryPlusNatIso_inv_app_hom, mapHomotopyCategoryPlusNatIso_hom_app_hom,
    mapHomotopyCategoryPlusCompIso_inv_app_hom, mapHomotopyCategoryPlusCompIso_hom_app_hom,
    mapHomotopyCategoryPlus_map_hom, mapHomotopyCategoryCompIso_inv_app,
    mapHomotopyCategoryCompIso_hom_app, mapHomotopyCategoryPlus_obj_obj_as,
    NatTrans.mapHomotopyCategory_app]
  exact congrArg (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
    (coherence_complex sq ea eb ec ed hcoh K.obj.as)

omit [b.PreservesInjectiveObjects] [d.PreservesInjectiveObjects] in
/-- The last leg of the left hand route: the unit of `Rg` at `b(a(K))`, the units of
`Rb` and of `Ra` and then the derived comparison of the square make up the degreewise comparison
of the square followed by the units of `Rg`, of `Rd` and of `Rc`. -/
private lemma derivedSquare_leg (sq : a ⋙ b ≅ c ⋙ d) (K : HomotopyCategory.Plus A) :
    g.rightDerivedFunctorPlusUnit.app
          (b.mapHomotopyCategoryPlus.obj (a.mapHomotopyCategoryPlus.obj K)) ≫
        g.rightDerivedFunctorPlus.map
          (b.rightDerivedFunctorPlusUnit.app (a.mapHomotopyCategoryPlus.obj K)) ≫
        g.rightDerivedFunctorPlus.map
          (b.rightDerivedFunctorPlus.map (a.rightDerivedFunctorPlusUnit.app K)) ≫
        g.rightDerivedFunctorPlus.map
          ((derivedSquare sq).hom.app (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map (g.mapHomotopyCategoryPlus.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (a ⋙ b))).hom.app K ≫
            (mapHomotopyCategoryPlusNatIso sq).hom.app K ≫
            (mapHomotopyCategoryPlusCompIso (Iso.refl (c ⋙ d))).inv.app K)) ≫
        g.rightDerivedFunctorPlusUnit.app
            (d.mapHomotopyCategoryPlus.obj (c.mapHomotopyCategoryPlus.obj K)) ≫
          g.rightDerivedFunctorPlus.map
            (d.rightDerivedFunctorPlusUnit.app (c.mapHomotopyCategoryPlus.obj K)) ≫
          g.rightDerivedFunctorPlus.map
            (d.rightDerivedFunctorPlus.map (c.rightDerivedFunctorPlusUnit.app K)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, unit_comp_derivedSquare sq K]
  simp only [Functor.map_comp, DerivedCategory.Plus.Qh.map_comp, Category.assoc]
  rw [reassoc_of% unit_naturality, reassoc_of% unit_naturality, reassoc_of% unit_naturality]
  rfl

omit [d.PreservesInjectiveObjects] in
/-- The left hand route of the square, computed after the derived-functor unit of `Rp`. -/
private lemma unit_comp_leftRoute (sq : a ⋙ b ≅ c ⋙ d) (ea : a ⋙ q ≅ p) (eb : b ⋙ g ≅ q)
    (K : HomotopyCategory.Plus A) :
    p.rightDerivedFunctorPlusUnit.app K ≫
        (derivedLeft ea).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        (derivedLeftTail eb).hom.app
          (a.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
        g.rightDerivedFunctorPlus.map
          ((derivedSquare sq).hom.app (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusNatIso ea).inv.app K ≫
            (mapHomotopyCategoryPlusCompIso (Iso.refl (a ⋙ q))).inv.app K ≫
            (mapHomotopyCategoryPlusNatIso eb).inv.app (a.mapHomotopyCategoryPlus.obj K) ≫
            (mapHomotopyCategoryPlusCompIso (Iso.refl (b ⋙ g))).inv.app
              (a.mapHomotopyCategoryPlus.obj K) ≫
            g.mapHomotopyCategoryPlus.map
              ((mapHomotopyCategoryPlusCompIso (Iso.refl (a ⋙ b))).hom.app K ≫
                (mapHomotopyCategoryPlusNatIso sq).hom.app K ≫
                (mapHomotopyCategoryPlusCompIso (Iso.refl (c ⋙ d))).inv.app K)) ≫
        g.rightDerivedFunctorPlusUnit.app
            (d.mapHomotopyCategoryPlus.obj (c.mapHomotopyCategoryPlus.obj K)) ≫
          g.rightDerivedFunctorPlus.map
            (d.rightDerivedFunctorPlusUnit.app (c.mapHomotopyCategoryPlus.obj K)) ≫
          g.rightDerivedFunctorPlus.map
            (d.rightDerivedFunctorPlus.map (c.rightDerivedFunctorPlusUnit.app K)) := by
  rw [← Category.assoc, unit_comp_derivedLeft ea K]
  simp only [Category.assoc]
  rw [reassoc_of% ((derivedLeftTail eb).hom.naturality (a.rightDerivedFunctorPlusUnit.app K)),
    reassoc_of% (unit_comp_derivedLeftTail eb (a.mapHomotopyCategoryPlus.obj K)),
    derivedSquare_leg sq K]
  simp only [Functor.map_comp, DerivedCategory.Plus.Qh.map_comp, Category.assoc]

/-- The right hand route of the square, computed after the derived-functor unit of `Rp`. -/
private lemma unit_comp_rightRoute (ec : c ⋙ r ≅ p) (ed : d ⋙ g ≅ r)
    (K : HomotopyCategory.Plus A) :
    p.rightDerivedFunctorPlusUnit.app K ≫
        (derivedRight ec).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        (derivedRightTail ed).hom.app
          (c.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusNatIso ec).inv.app K ≫
            (mapHomotopyCategoryPlusCompIso (Iso.refl (c ⋙ r))).inv.app K ≫
            (mapHomotopyCategoryPlusNatIso ed).inv.app (c.mapHomotopyCategoryPlus.obj K) ≫
            (mapHomotopyCategoryPlusCompIso (Iso.refl (d ⋙ g))).inv.app
              (c.mapHomotopyCategoryPlus.obj K)) ≫
        g.rightDerivedFunctorPlusUnit.app
            (d.mapHomotopyCategoryPlus.obj (c.mapHomotopyCategoryPlus.obj K)) ≫
          g.rightDerivedFunctorPlus.map
            (d.rightDerivedFunctorPlusUnit.app (c.mapHomotopyCategoryPlus.obj K)) ≫
          g.rightDerivedFunctorPlus.map
            (d.rightDerivedFunctorPlus.map (c.rightDerivedFunctorPlusUnit.app K)) := by
  rw [← Category.assoc, unit_comp_derivedRight ec K]
  simp only [Category.assoc]
  have hnat : r.rightDerivedFunctorPlus.map (c.rightDerivedFunctorPlusUnit.app K) ≫
      (derivedRightTail ed).hom.app
        (c.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (derivedRightTail ed).hom.app
          (DerivedCategory.Plus.Qh.obj (c.mapHomotopyCategoryPlus.obj K)) ≫
        g.rightDerivedFunctorPlus.map
          (d.rightDerivedFunctorPlus.map (c.rightDerivedFunctorPlusUnit.app K)) :=
    (derivedRightTail ed).hom.naturality (c.rightDerivedFunctorPlusUnit.app K)
  rw [hnat, reassoc_of% (unit_comp_derivedRightTail ed (c.mapHomotopyCategoryPlus.obj K))]
  simp only [DerivedCategory.Plus.Qh.map_comp, Category.assoc]

/-- **The derived coherence square commutes.**  Given the underived coherence
`eb.hom.app (a X) ≫ ea.hom.app X = g (sq.hom.app X) ≫ ed.hom.app (c X) ≫ ec.hom.app X`, the two
routes `Rp ⟶ Rc ⋙ Rd ⋙ Rg` built from the five derived comparisons agree. -/
theorem derived_coherence (sq : a ⋙ b ≅ c ⋙ d) (ea : a ⋙ q ≅ p) (eb : b ⋙ g ≅ q)
    (ec : c ⋙ r ≅ p) (ed : d ⋙ g ≅ r)
    (hcoh : ∀ X : A, eb.hom.app (a.obj X) ≫ ea.hom.app X =
      g.map (sq.hom.app X) ≫ ed.hom.app (c.obj X) ≫ ec.hom.app X) :
    (derivedLeft ea).hom ≫
        Functor.whiskerLeft a.rightDerivedFunctorPlus (derivedLeftTail eb).hom ≫
        Functor.whiskerRight (derivedSquare sq).hom g.rightDerivedFunctorPlus =
      (derivedRight ec).hom ≫
        Functor.whiskerLeft c.rightDerivedFunctorPlus (derivedRightTail ed).hom := by
  refine Functor.rightDerived_ext p.rightDerivedFunctorPlus p.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso A) _ _ _ (NatTrans.ext (funext fun K ↦ ?_))
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [unit_comp_leftRoute sq ea eb K, unit_comp_rightRoute ec ed K,
    coherence_homotopy sq ea eb ec ed hcoh K]

end Square

end Stacks.DerivedFunctor.LeraySquare

end
