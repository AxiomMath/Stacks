module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPostcomposeExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompIsoSpellings
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerivedNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyFactorsh
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPostcomposeIndexing

/-!
# Post-composition with an exact functor, and the derived/classical bridge

Let `w : A ⥤ B` be additive with `A` having enough injectives, let `Rw : D(A) ⥤ D(B)` be a right
derived functor of `w` with unit `α`, and let `G : B ⥤ C` be additive and exact. There are two
routes from `Hⁿ(G.mapDerivedCategory (Rw (X[0])))` to `Rⁿ(w ⋙ G)(X)`:

* the bridge `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` for `w ⋙ G`,
  taken at `Rw ⋙ G.mapDerivedCategory` — which is a right derived functor of `w ⋙ G` by
  `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`, with unit
  `Stacks.DerivedFunctor.postcomposeUnit`; and
* pulling `G` out of the homology of the derived category by
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, applying the bridge for `w` under `G`,
  and pulling `G` out of the right derived functor by
  `CategoryTheory.Functor.rightDerivedCompIso`.

They agree: that is `singleCompDerivedCompHomologyIsoRightDerived_postComp_app`, the main result.
It is the **post-composition** coherence for the bridge, the last of the three the implementation
notes of `Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision` ask for — the
degreewise one is
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality` and the
pre-composition one is
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp`.

## Main results

* `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app`: **the
  bridge carries post-composition with an exact functor to
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` followed by
  `CategoryTheory.Functor.rightDerivedCompIso`.**

## Implementation notes

The two sides are four-factor composites, by
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app`, and the proof is
the same four-square ladder as the pre-composition coherence:

* the first square is the naturality of
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at `Rw` applied to the augmentation
  `Stacks.DerivedFunctor.singleIsoResCompQh`;
* the second is its naturality at the unit of `Rw` on the chosen resolution, which is where
  `Stacks.DerivedFunctor.postcomposeUnit_app` enters: the unit of `Rw ⋙ G.mapDerivedCategory` is
  `G.mapDerivedCategoryFactorsh` inverted followed by `G.mapDerivedCategory` applied to the unit
  of `Rw`, so its inverse splits into the two factors the square needs;
* the third is `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_hom_app_Qh`, which says
  precisely how the comparison interacts with the two factorisations through the homotopy
  category — the only non-formal input, and the reason that statement was proved;
* the fourth is the classical, `ℕ`-indexed half
  `Stacks.DerivedIndexing.rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes`, read as a
  computation of the inverse of `Stacks.DerivedIndexing.rightDerivedIsoRes` for `w ⋙ G`.

**Every step is a helper at a variable category, applied with `exact`.** `sq_one`, `sq_two`,
`sq_three`, `sq_four`, `paste_ladder`, `map_comp_id`, `map_split` and `inv_of_hom_eq` are stated
at arbitrary categories with the objects implicit and the morphisms explicit, so that applying
one never asks the elaborator to solve for an object across the two spellings of
`Qh.obj ((w.mapHomotopyCategory _ ⋙ G.mapHomotopyCategory _).obj K)`.

**The `IsRightDerivedFunctor` instance for the composite is a hypothesis**, exactly as `α'` is in
the pre-composition coherence: it is always available from
`Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`, and taking it as an instance argument
keeps the K-injective resolution hypothesis out of the statement twice over. The class is a
`Prop`, so no coherence between two such instances has to be checked.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedIndexing

universe wA vA uA wB vB uB wC vC uC

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  (w : A ⥤ B) [w.Additive] (G : B ⥤ C) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(Rw ⋙ G.mapDerivedCategory).IsRightDerivedFunctor
    (Stacks.DerivedFunctor.postcomposeUnit w G Rw α)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- The first square: a naturality square whose right edge is inverted. Stated at an arbitrary
category with the objects implicit and the morphisms explicit. -/
private theorem sq_one {E : Type*} [Category* E] {x x' y z : E} (v : x ⟶ x') (b : x' ⟶ z)
    (a : x ⟶ y) (q : y ⟶ z) (r : z ⟶ y) (hnat : a ≫ q = v ≫ b)
    (hqr : q ≫ r = CategoryStruct.id y) : v ≫ b ≫ r = a := by
  rw [← reassoc_of% hnat, hqr, Category.comp_id]

/-- The second square: a naturality square whose left vertical edge is split in two by the
computation `ha` of that edge. Stated at an arbitrary category. -/
private theorem sq_two {E : Type*} [Category* E] {p q r s t : E} (c : p ⟶ q) (m : q ⟶ r)
    (dd : r ⟶ s) (b : p ⟶ t) (ci : t ⟶ r) (a : q ⟶ s)
    (ha : a = m ≫ dd) (hnat : b ≫ ci = c ≫ m) :
    c ≫ a = b ≫ ci ≫ dd := by
  rw [ha, reassoc_of% hnat]

/-- The third square, read off a computation of one isomorphism as a four-factor composite: with
`hh` the composite `P ≫ Q ≫ R ≫ S` and `R`, `S` invertible, inverting `hh` and cancelling the
last two factors leaves `(ii ≫ P) ≫ Q = S' ≫ R'`. Stated at an arbitrary category. -/
private theorem sq_three {E : Type*} [Category* E] {x y z u v : E}
    (ii : x ⟶ y) (hh : y ⟶ x) (P : y ⟶ z) (Q : z ⟶ u) (R : u ⟶ v) (R' : v ⟶ u)
    (S : v ⟶ x) (S' : x ⟶ v)
    (hhom : hh = P ≫ Q ≫ R ≫ S) (hih : ii ≫ hh = CategoryStruct.id x)
    (hRR : R ≫ R' = CategoryStruct.id u) (hSS : S ≫ S' = CategoryStruct.id v) :
    (ii ≫ P) ≫ Q = S' ≫ R' := by
  calc (ii ≫ P) ≫ Q = (ii ≫ hh) ≫ S' ≫ R' := by
        simp [hhom, reassoc_of% hSS, hRR]
    _ = S' ≫ R' := by rw [hih, Category.id_comp]

/-- The fourth square: a three-factor computation of an isomorphism `D`, read as the square
relating the inverse of `D` to the inverses of the first two factors. Stated at an arbitrary
category. -/
private theorem sq_four {E : Type*} [Category* E] {x y z t : E}
    (A₀ : x ⟶ y) (A' : y ⟶ x) (B₀ : y ⟶ z) (B' : z ⟶ y) (Cc : z ⟶ t) (D : x ⟶ t) (D' : t ⟶ x)
    (hABC : A₀ ≫ B₀ ≫ Cc = D) (hA : A' ≫ A₀ = CategoryStruct.id y)
    (hB : B' ≫ B₀ = CategoryStruct.id z) (hD : D ≫ D' = CategoryStruct.id x) :
    Cc ≫ D' = B' ≫ A' := by
  calc Cc ≫ D' = B' ≫ A' ≫ (A₀ ≫ B₀ ≫ Cc) ≫ D' := by
        simp [reassoc_of% hA, reassoc_of% hB]
    _ = B' ≫ A' := by rw [hABC, hD, Category.comp_id]

/-- Four squares pasted, in the shape in which
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app` produces the two
sides: the leftmost is the computation of `a₁` and the rightmost the computation of `b₄`. Stated
at an arbitrary category with the objects implicit and the morphisms explicit. -/
private theorem paste_ladder {E : Type*} [Category* E] {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ : E}
    (v₀ : X₀ ⟶ Y₀) (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (a₃ : X₂ ⟶ X₃) (a₄ : X₃ ⟶ X₄)
    (b₁ : Y₀ ⟶ Y₁) (b₂ : Y₁ ⟶ Y₂) (b₃ : Y₂ ⟶ Y₃) (b₄ : Y₃ ⟶ X₄)
    (c₁ : Y₁ ⟶ X₁) (c₂ : Y₂ ⟶ X₂) (c₃ : Y₃ ⟶ X₃)
    (h₁ : v₀ ≫ b₁ ≫ c₁ = a₁) (h₂ : c₁ ≫ a₂ = b₂ ≫ c₂) (h₃ : c₂ ≫ a₃ = b₃ ≫ c₃)
    (h₄ : c₃ ≫ a₄ = b₄) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ = v₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ := by
  rw [← h₁, ← h₄]
  simp only [Category.assoc, reassoc_of% h₂, reassoc_of% h₃]

/-- A functor applied to a four-factor composite, followed by one more morphism. Stated at
arbitrary categories. -/
private theorem map_split {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {a b c d e : D} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e) {z : E}
    (m : H.obj e ⟶ z) :
    H.map (f ≫ g ≫ h ≫ k) ≫ m = H.map f ≫ H.map g ≫ H.map h ≫ H.map k ≫ m := by
  simp

/-- The inverse of an isomorphism whose `hom` is a composite of two isomorphisms. Stated at an
arbitrary category; it is `CategoryTheory.Iso.ext` followed by the definitional computation of the
inverse of a composite. -/
private theorem inv_of_hom_eq {E : Type*} [Category* E] {x y z : E} (e : x ≅ z) (p : x ≅ y)
    (q : y ≅ z) (h : e.hom = p.hom ≫ q.hom) : e.inv = q.inv ≫ p.inv :=
  congrArg Iso.inv (Iso.ext h : e = p ≪≫ q)

/-- **The bridge `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)` carries post-composition with an exact functor to
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` and
`CategoryTheory.Functor.rightDerivedCompIso.`** For `w : A ⥤ B` additive and `G : B ⥤ C` additive
and exact, the bridge for `w ⋙ G` taken at `Rw ⋙ G.mapDerivedCategory` is: pull `G` out of the
homology of `D(C)`, apply the bridge for `w` under `G`, and pull `G` out of the right derived
functor.

Together with
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality` and
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp` this completes the
three coherences for the bridge. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_postComp_app (n : ℕ) (X : A) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (w ⋙ G)
        (Rw ⋙ G.mapDerivedCategory) (Stacks.DerivedFunctor.postcomposeUnit w G Rw α)
        hres n).hom.app X =
      (G.mapDerivedCategoryHomologyIso (n : ℤ)).hom.app
          (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)) ≫
        G.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw α
            hres n).hom.app X) ≫
          (w.rightDerivedCompIso G n).inv.app X := by
  have huwg : (Stacks.DerivedFunctor.resCompUnitIso (w ⋙ G) (Rw ⋙ G.mapDerivedCategory)
        (Stacks.DerivedFunctor.postcomposeUnit w G Rw α) hres).inv.app X =
      G.mapDerivedCategory.map ((Stacks.DerivedFunctor.resCompUnitIso w Rw α hres).inv.app X) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X)) :=
    inv_of_hom_eq
      ((Stacks.DerivedFunctor.resCompUnitIso (w ⋙ G) (Rw ⋙ G.mapDerivedCategory)
        (Stacks.DerivedFunctor.postcomposeUnit w G Rw α) hres).app X)
      (G.mapDerivedCategoryFactorsh.app
        ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X))).symm
      (G.mapDerivedCategory.mapIso ((Stacks.DerivedFunctor.resCompUnitIso w Rw α hres).app X))
      (Stacks.DerivedFunctor.postcomposeUnit_app w G Rw α (resH.obj X))
  have h₁ := sq_one
    ((G.mapDerivedCategoryHomologyIso (n : ℤ)).hom.app
      (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)))
    (G.map ((DerivedCategory.homologyFunctor B (n : ℤ)).map
      (Rw.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app X))))
    ((DerivedCategory.homologyFunctor C (n : ℤ)).map
      ((Rw ⋙ G.mapDerivedCategory).map
        ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app X)))
    ((G.mapDerivedCategoryHomologyIso (n : ℤ)).hom.app
      (Rw.obj (DerivedCategory.Qh.obj (resH.obj X))))
    ((G.mapDerivedCategoryHomologyIso (n : ℤ)).inv.app
      (Rw.obj (DerivedCategory.Qh.obj (resH.obj X))))
    ((G.mapDerivedCategoryHomologyIso (n : ℤ)).hom.naturality
      (Rw.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app X)))
    (Iso.hom_inv_id_app _ _)
  have h₂ := sq_two
    ((G.mapDerivedCategoryHomologyIso (n : ℤ)).inv.app
      (Rw.obj (DerivedCategory.Qh.obj (resH.obj X))))
    ((DerivedCategory.homologyFunctor C (n : ℤ)).map (G.mapDerivedCategory.map
      ((Stacks.DerivedFunctor.resCompUnitIso w Rw α hres).inv.app X)))
    ((DerivedCategory.homologyFunctor C (n : ℤ)).map
      (G.mapDerivedCategoryFactorsh.hom.app
        ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X))))
    (G.map ((DerivedCategory.homologyFunctor B (n : ℤ)).map
      ((Stacks.DerivedFunctor.resCompUnitIso w Rw α hres).inv.app X)))
    ((G.mapDerivedCategoryHomologyIso (n : ℤ)).inv.app
      (DerivedCategory.Qh.obj ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X))))
    ((DerivedCategory.homologyFunctor C (n : ℤ)).map
      ((Stacks.DerivedFunctor.resCompUnitIso (w ⋙ G) (Rw ⋙ G.mapDerivedCategory)
        (Stacks.DerivedFunctor.postcomposeUnit w G Rw α) hres).inv.app X))
    ((congrArg (DerivedCategory.homologyFunctor C (n : ℤ)).map huwg).trans
      ((DerivedCategory.homologyFunctor C (n : ℤ)).map_comp _ _))
    ((G.mapDerivedCategoryHomologyIso (n : ℤ)).inv.naturality
      ((Stacks.DerivedFunctor.resCompUnitIso w Rw α hres).inv.app X))
  have h₃ := sq_three
    ((G.mapDerivedCategoryHomologyIso (n : ℤ)).inv.app
      (DerivedCategory.Qh.obj ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X))))
    ((G.mapDerivedCategoryHomologyIso (n : ℤ)).hom.app
      (DerivedCategory.Qh.obj ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X))))
    ((DerivedCategory.homologyFunctor C (n : ℤ)).map
      (G.mapDerivedCategoryFactorsh.hom.app
        ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X))))
    ((DerivedCategory.homologyFunctorFactorsh C (n : ℤ)).hom.app
      ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X))))
    ((G.mapHomotopyCategoryHomologyIso (ComplexShape.up ℤ) (n : ℤ)).hom.app
      ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X)))
    ((G.mapHomotopyCategoryHomologyIso (ComplexShape.up ℤ) (n : ℤ)).inv.app
      ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X)))
    (G.map ((DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).inv.app
      ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X))))
    (G.map ((DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
      ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X))))
    (G.mapDerivedCategoryHomologyIso_hom_app_Qh (n : ℤ)
      ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X)))
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _)
    (map_comp_id G _ _ (Iso.inv_hom_id_app _ _))
  have h₄ := sq_four
    ((w.rightDerivedCompIso G n).hom.app X) ((w.rightDerivedCompIso G n).inv.app X)
    (G.map ((rightDerivedIsoRes w n).hom.app X))
    (G.map ((rightDerivedIsoRes w n).inv.app X))
    ((G.mapHomotopyCategoryHomologyIso (ComplexShape.up ℤ) (n : ℤ)).inv.app
      ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X)))
    ((rightDerivedIsoRes (w ⋙ G) n).hom.app X) ((rightDerivedIsoRes (w ⋙ G) n).inv.app X)
    (rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes w G n X)
    (Iso.inv_hom_id_app _ _) (map_comp_id G _ _ (Iso.inv_hom_id_app _ _))
    (Iso.hom_inv_id_app _ _)
  rw [Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app,
    Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app, map_split]
  exact paste_ladder _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

end Stacks.DerivedIndexing

end
