module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerivedNaturality
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Varying the underived functor in the bridge `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)`

Let `A` and `B` be abelian categories with unbounded derived categories, `A` with enough
injectives, and let `R : D(A) ⥤ D(B)` be a right derived functor of **two** additive functors
`S', S : A ⥤ B` which are isomorphic, `e : S' ≅ S`, the two units `α'` and `α` being related by
`e`: `α` is the degreewise action of `e.inv` followed by `α'`.  Then the two bridges
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` differ exactly by the
degree-`n` right derived functor of `e`.

This is the third coherence the bridge needs, beside
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp` and
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app`: those two
vary the functor by composing with an exact functor on either side, whereas the situation here is
that one derived functor is presented as a right derived functor of two *different* spellings of
one underived functor.  It arises whenever a composite `w ⋙ G` is identified with an endofunctor
by a non-trivial isomorphism — for instance abelian sections supported on a closed subset,
realized on that subset and pushed forward, against the supported-sections endofunctor.

## Main results

* `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app`: **the
  bridge at `S` is the bridge at `S'` followed by `CategoryTheory.NatTrans.rightDerived e.hom n`.**
  The natural-isomorphism form is
  `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_sourceCongr`.

## Implementation notes

The bridge depends on its unit only through
`Stacks.DerivedFunctor.resCompUnitIso`, which is the unit whiskered with the chosen extended
injective resolution; so the hypothesis relating `α` to `α'` is used once, at the resolution of
the object.  What is left is a two-square ladder: the naturality of
`CategoryTheory.DerivedCategory.homologyFunctorFactorsh` at the degreewise action of `e.hom`, and
the naturality of `Stacks.DerivedIndexing.rightDerivedIsoRes` in the functor variable, which is
`Stacks.DerivedIndexing.rightDerivedIsoRes_hom_app_naturality`.

Every rearrangement is a `private` lemma stated at a variable category with the objects implicit
and the morphisms explicit, applied with `exact`: the composites involve the two spellings
`(S.mapHomotopyCategory c).obj K` and `S.mapHomologicalComplex c` of one object, across which a
rewrite in place is not type-correct.  This is the house style of
`StacksFrontier.Homology.DerivedIndexing.PostCompositionCoherence`.

**No `@[stacks ...]` attribute is attached to any declaration here.**
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedIndexing

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- The inverse of an isomorphism whose `hom` is a fixed morphism followed by the `hom` of
another, that morphism having a right inverse.  Stated at an arbitrary category with the objects
implicit, the insertion happening across two spellings of one object. -/
private theorem inv_eq_of_hom_eq {E : Type*} [Category* E] {x y z : E} (p : y ≅ x) (q : z ≅ x)
    (u : y ⟶ z) (v : z ⟶ y) (h : p.hom = u ≫ q.hom) (huv : u ≫ v = CategoryStruct.id y) :
    p.inv = q.inv ≫ v := by
  rw [← cancel_epi p.hom, p.hom_inv_id, h, Category.assoc, Iso.hom_inv_id_assoc, huv]

/-- A commuting square with invertible horizontal edges, transported to the inverses.  Stated at
an arbitrary category. -/
private theorem comm_inv_of_comm {E : Type*} [Category* E] {x₁ x₂ y₁ y₂ : E}
    (u₁ : x₁ ≅ y₁) (u₂ : x₂ ≅ y₂) (g : x₁ ⟶ x₂) (f : y₁ ⟶ y₂)
    (h : g ≫ u₂.hom = u₁.hom ≫ f) : f ≫ u₂.inv = u₁.inv ≫ g := by
  rw [← cancel_epi u₁.hom, ← Category.assoc, ← h, Category.assoc, u₂.hom_inv_id,
    Category.comp_id, ← Category.assoc, u₁.hom_inv_id, Category.id_comp]

/-- Two squares pasted, in the shape the two sides of the bridge produce: the second factor of
the `S`-side is split by the comparison, and the remaining two squares cross it to the `S'`-side.
Stated at an arbitrary category with the objects implicit and the morphisms explicit. -/
private theorem paste_two {E : Type*} [Category* E] {x p q q' r r' s s' : E}
    (a : x ⟶ p) (b : p ⟶ q) (v : q ⟶ q') (c : q' ⟶ r) (d : r ⟶ s)
    (c' : q ⟶ r') (m : r' ⟶ r) (d' : r' ⟶ s') (ee : s' ⟶ s)
    (h₁ : v ≫ c = c' ≫ m) (h₂ : m ≫ d = d' ≫ ee) :
    a ≫ (b ≫ v) ≫ c ≫ d = (a ≫ b ≫ c' ≫ d') ≫ ee := by
  simp only [Category.assoc, reassoc_of% h₁, h₂]

variable (S' S : A ⥤ B) [S'.Additive] [S.Additive] (e : S' ≅ S)
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (α' : S'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  (α : S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  [R.IsRightDerivedFunctor α' (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

omit [EnoughInjectives A] [HasDerivedCategory A] in
/-- The degreewise actions of `e.inv` and of `e.hom` on the homotopy category, read in the
derived category, are mutually inverse. -/
private theorem qh_map_mapHomotopyCategory_inv_hom
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) =
      CategoryStruct.id
        (DerivedCategory.Qh.obj ((S.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) := by
  rw [← DerivedCategory.Qh.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id,
    NatTrans.id_app, DerivedCategory.Qh.map_id]

/-- **Varying the underived functor in the bridge, componentwise.**  If `R` is a right derived
functor of `S` with unit `α` and of `S'` with unit `α'`, and `α` is the degreewise action of
`e.inv` followed by `α'`, then the bridge `Hⁿ(R(X[0])) ≅ RⁿS(X)` is the bridge
`Hⁿ(R(X[0])) ≅ RⁿS'(X)` followed by `CategoryTheory.NatTrans.rightDerived e.hom n`. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app
    (hα : ∀ K : HomotopyCategory A (ComplexShape.up ℤ), α.app K =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app K) ≫ α'.app K)
    (n : ℕ) (X : A) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S R α hres n).hom.app X =
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S' R α'
          hres n).hom.app X ≫
        (NatTrans.rightDerived e.hom n).app X := by
  -- the comparison at the chosen extended injective resolution of `X`
  have hι : (Stacks.DerivedFunctor.resCompUnitIso S R α hres).inv.app X =
      (Stacks.DerivedFunctor.resCompUnitIso S' R α' hres).inv.app X ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app (resH.obj X)) :=
    inv_eq_of_hom_eq ((Stacks.DerivedFunctor.resCompUnitIso S R α hres).app X)
      ((Stacks.DerivedFunctor.resCompUnitIso S' R α' hres).app X) _ _ (hα (resH.obj X))
      (qh_map_mapHomotopyCategory_inv_hom S' S e (resH.obj X))
  -- the first square: the factorisation of the cohomology functor is natural
  have h₁ := (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.naturality
    ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app (resH.obj X))
  -- the second square: `rightDerivedIsoRes` is natural in the functor variable
  have h₂ : (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app (resH.obj X)) ≫
        (rightDerivedIsoRes S n).inv.app X =
      (rightDerivedIsoRes S' n).inv.app X ≫ (NatTrans.rightDerived e.hom n).app X :=
    comm_inv_of_comm ((rightDerivedIsoRes S' n).app X) ((rightDerivedIsoRes S n).app X) _ _
      (rightDerivedIsoRes_hom_app_naturality e.hom n X)
  rw [Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app,
    Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app, hι,
    (DerivedCategory.homologyFunctor B (n : ℤ)).map_comp]
  exact paste_two _ _ _ _ _ _ _ _ _ h₁ h₂

/-- **Varying the underived functor in the bridge.**  The natural-isomorphism form of
`singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app`. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_sourceCongr
    (hα : ∀ K : HomotopyCategory A (ComplexShape.up ℤ), α.app K =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app K) ≫ α'.app K)
    (n : ℕ) :
    Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S R α hres n =
      Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S' R α' hres n ≪≫
        Functor.rightDerivedIsoOfNatIso e n :=
  Iso.ext (NatTrans.ext (funext fun X =>
    singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app S' S e R α' α hres hα n X))

end Stacks.DerivedIndexing

end
