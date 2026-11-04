module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryFactorshQuotient
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeDegreewise
public import StacksFrontier.CategoryTheory.Adjunction.MateTransport
public import StacksFrontier.CategoryTheory.Localization.NatTransMapDerivedCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeSquareDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroCounitTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactAdjunctionDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetRestrictionOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedTensor

/-!
# The derived base change of the restriction square is the derived image of the underived one

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be an open immersion of ringed spaces, `Z ⊆ X` a closed
subset with closed preimage `Z' = f^{-1}(Z)`, and write

```
  (Z', 𝒪_{X'}|_{Z'}) --- i' ---> X'
       |                         |
       r = f|_{Z'}               f
       |                         |
  (Z, 𝒪_X|_Z) --------- i -----> X
```

for the Cartesian square of the restriction, `w : r ≫ i = i' ≫ f`.  Over it sit two base change
maps.  Underived, `closedSubsetPushforwardPullbackNatIso` is the isomorphism
`i_* ⋙ f^* ≅ r^* ⋙ i'_*`; derived, `supportedPullbackBaseChangeMap` is the map
`Lf^*(Ri_*N) ⟶ Ri'_*(Lr^*N)` of [Stacks, Tag 08HY].  All four of `f^*`, `r^*`, `i^*`, `i'^*`
are exact — the first two because `f` and `r` are open immersions, the last two unconditionally
— and `i_*`, `i'_*` are exact because `Z` and `Z'` are closed; so each of the six derived
functors involved is the functor induced degreewise, and the main result of this file says that
under those identifications the derived base change **is** the derived image of the underived
one.

## Main results

* `Stacks.Homology.mapDerivedCategoryIsoOfIso_hom`: the isomorphism of induced functors
  attached to an isomorphism of exact functors is `CategoryTheory.NatTrans.mapDerivedCategory`
  of that isomorphism.  This is what was missing for the two derived 2-squares of the
  development to meet.
* `Stacks.Homology.mapDerivedCategoryTwoSquareOfIso_eq`: **the two derived images of an
  invertible 2-square agree** — `Stacks.Homology.mapDerivedCategoryTwoSquareOfIso` is
  `CategoryTheory.TwoSquare.mapDerivedCategory`.
* `CategoryTheory.TwoSquare.mapDerivedCategory_app_Qh`: the derived 2-square on the image of
  `DerivedCategory.Qh`, the analogue over `DerivedCategory.Qh` of
  `CategoryTheory.TwoSquare.mapDerivedCategory_app_Q`.
* `CategoryTheory.mateEquiv_transport_app`: **the mate of a 2-square read at all six functors
  replaced by isomorphic ones**, the three statements of
  `StacksFrontier/CategoryTheory/Adjunction/MateTransport.lean` applied in turn.
* `Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare_eq` and
  `Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare_app`: the derived comparison of
  iterated pullbacks around any commutative square, as a derived 2-square and at an object.
* `Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mapDerivedCategory`:
  **the derived base change map of [Stacks, Tag 08HY] for the restriction square is the derived
  image of the underived base change map.**
* `Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mapDerivedCategory_Qh`:
  the same equation on the image of `DerivedCategory.Qh`, with the right-hand side written out
  on the homotopy category.

## Implementation notes

**Why so many small steps.**  The categories here are large enough that a single `rfl` between
two spellings of the base change map exhausts the *kernel's* reduction budget when it sits inside
a statement that writes the whole composite:
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare_eq_mateEquiv` and
`Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mateEquiv_app` are that
one unfolding, split in two and performed in statements that write nothing else.  Every diagram
chase is likewise hoisted into a `private` theorem at a variable category with the objects
implicit and the morphisms explicit, so that it applies by a single `exact` and no rewriting
happens in a goal that mentions a derived category.

**Both pushforward-exactness instances come from `hZ` and `hZ'`**, by
`Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits`, and are introduced
by `letI` in the statements that need them rather than assumed.

## References

* [Stacks Project, Remark 20.28.3 (Tag 08HY)](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Lemma 20.28.6 (Tag 079W)](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.Homology

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- The chase behind `Stacks.Homology.mapDerivedCategoryIsoOfIso_hom`: the universal property
at the quotient of a complex, the two crossings of the structure maps and the crossing of the
degreewise comparison, followed by three cancellations.  Stated at an arbitrary category with
the objects implicit and the morphisms explicit, so that it applies by `exact`. -/
private theorem iso_chase {D : Type*} [Category D]
    {a₁ a₂ b₁ b₂ d dh e₂ z : D}
    (t₁ : a₁ ⟶ b₁) (t₂ : a₂ ⟶ b₂) (a : a₁ ⟶ a₂) (a' : a₂ ⟶ a₁) (b : b₁ ⟶ b₂)
    (fh : a₁ ⟶ dh) (gh : b₁ ⟶ z) (m : dh ⟶ z) (f : a₂ ⟶ d) (v : d ⟶ dh) (v' : dh ⟶ d)
    (n : d ⟶ e₂) (g : b₂ ⟶ e₂) (g' : e₂ ⟶ b₂) (w : e₂ ⟶ z) (w' : z ⟶ e₂)
    (hUP : t₁ ≫ gh = fh ≫ m) (hgh : gh = b ≫ g ≫ w) (hfh : fh = a ≫ f ≫ v)
    (hm : m = v' ≫ n ≫ w) (hnat : t₁ ≫ b = a ≫ t₂)
    (hv : v ≫ v' = 𝟙 d) (hw : w ≫ w' = 𝟙 e₂) (ha : a' ≫ a = 𝟙 a₂) (hg : g ≫ g' = 𝟙 b₂) :
    t₂ = f ≫ n ≫ g' := by
  have h1 : a ≫ t₂ ≫ g ≫ w = a ≫ f ≫ n ≫ w := by
    calc a ≫ t₂ ≫ g ≫ w = (a ≫ t₂) ≫ g ≫ w := by rw [Category.assoc]
      _ = (t₁ ≫ b) ≫ g ≫ w := by rw [hnat]
      _ = t₁ ≫ b ≫ g ≫ w := by rw [Category.assoc]
      _ = t₁ ≫ gh := by rw [hgh]
      _ = fh ≫ m := hUP
      _ = (a ≫ f ≫ v) ≫ v' ≫ n ≫ w := by rw [hfh, hm]
      _ = a ≫ f ≫ (v ≫ v') ≫ n ≫ w := by simp only [Category.assoc]
      _ = a ≫ f ≫ n ≫ w := by rw [hv, Category.id_comp]
  have h2 : t₂ ≫ g ≫ w = f ≫ n ≫ w := by
    calc t₂ ≫ g ≫ w = (a' ≫ a) ≫ t₂ ≫ g ≫ w := by rw [ha, Category.id_comp]
      _ = a' ≫ a ≫ t₂ ≫ g ≫ w := by rw [Category.assoc]
      _ = a' ≫ a ≫ f ≫ n ≫ w := by rw [h1]
      _ = (a' ≫ a) ≫ f ≫ n ≫ w := by rw [Category.assoc]
      _ = f ≫ n ≫ w := by rw [ha, Category.id_comp]
  have h3 : t₂ ≫ g = f ≫ n := by
    calc t₂ ≫ g = (t₂ ≫ g) ≫ w ≫ w' := by rw [hw, Category.comp_id]
      _ = (t₂ ≫ g ≫ w) ≫ w' := by simp only [Category.assoc]
      _ = (f ≫ n ≫ w) ≫ w' := by rw [h2]
      _ = (f ≫ n) ≫ w ≫ w' := by simp only [Category.assoc]
      _ = f ≫ n := by rw [hw, Category.comp_id]
  calc t₂ = t₂ ≫ g ≫ g' := by rw [hg, Category.comp_id]
    _ = (t₂ ≫ g) ≫ g' := by rw [Category.assoc]
    _ = (f ≫ n) ≫ g' := by rw [h3]
    _ = f ≫ n ≫ g' := by rw [Category.assoc]

section TwoSquare

variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {E : Type u₄} [Category.{v₄} E] [Abelian E] [HasDerivedCategory.{w₄} E]

/-- **The two derived images of a 2-square of exact functors whose transformation is invertible
agree.**  `Stacks.Homology.mapDerivedCategoryTwoSquareOfIso` is assembled from the composition
comparison built out of the uniqueness of a left derived functor and from
`Stacks.Homology.mapDerivedCategoryIsoOfIso`, while
`CategoryTheory.TwoSquare.mapDerivedCategory` is assembled from
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and
`CategoryTheory.NatTrans.mapDerivedCategory`.  The two composition comparisons are identified by
`Stacks.Homology.mapDerivedCategoryCompIso_refl_eq` and the two middle factors by
`Stacks.Homology.mapDerivedCategoryIsoOfIso_hom`. -/
theorem mapDerivedCategoryTwoSquareOfIso_eq (T : A ⥤ B) (L : A ⥤ C) (R : B ⥤ E) (Bo : C ⥤ E)
    [T.Additive] [L.Additive] [R.Additive] [Bo.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits Bo] [PreservesFiniteColimits Bo]
    (α : T ⋙ R ≅ L ⋙ Bo) :
    mapDerivedCategoryTwoSquareOfIso T L R Bo α =
      CategoryTheory.TwoSquare.mapDerivedCategory (TwoSquare.mk _ _ _ _ α.hom) := by
  show (mapDerivedCategoryCompIso T R (T ⋙ R) (Iso.refl _)).hom ≫
        (mapDerivedCategoryIsoOfIso (T ⋙ R) (L ⋙ Bo) α).hom ≫
        (mapDerivedCategoryCompIso L Bo (L ⋙ Bo) (Iso.refl _)).inv =
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso T R).inv ≫
        NatTrans.mapDerivedCategory α.hom ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso L Bo).hom
  rw [mapDerivedCategoryIsoOfIso_hom, mapDerivedCategoryCompIso_refl_eq T R,
    mapDerivedCategoryCompIso_refl_eq L Bo]
  rfl

/-- The chase behind `CategoryTheory.TwoSquare.mapDerivedCategory_app_Qh`: the two composition
comparisons are replaced by their universal properties and the three pairs of mutually inverse
morphisms that remain are cancelled.  Stated at an arbitrary category with the objects implicit
and the morphisms explicit, so that it applies by `exact`. -/
private theorem qh_chase {D : Type*} [Category D] {s p r t x y m n : D}
    (cT : s ⟶ p) (nt : p ⟶ r) (cL : r ⟶ t) (cL' : t ⟶ r) (P : p ⟶ x) (q : x ⟶ y)
    (QQ : r ⟶ y) (a₁ : s ⟶ m) (a₂ : m ⟶ x) (b₁ : t ⟶ n) (b₂ : n ⟶ y) (b₂' : y ⟶ n)
    (b₁' : n ⟶ t)
    (hT : cT ≫ P = a₁ ≫ a₂) (hα : P ≫ q = nt ≫ QQ) (hL : cL' ≫ QQ = b₁ ≫ b₂)
    (hinv : cL ≫ cL' = 𝟙 r) (hb2 : b₂ ≫ b₂' = 𝟙 n) (hb1 : b₁ ≫ b₁' = 𝟙 t) :
    cT ≫ nt ≫ cL = a₁ ≫ a₂ ≫ q ≫ b₂' ≫ b₁' := by
  have hq : QQ ≫ b₂' ≫ b₁' = cL := by
    calc QQ ≫ b₂' ≫ b₁' = (cL ≫ cL') ≫ QQ ≫ b₂' ≫ b₁' := by rw [hinv, Category.id_comp]
      _ = cL ≫ (cL' ≫ QQ) ≫ b₂' ≫ b₁' := by simp only [Category.assoc]
      _ = cL ≫ (b₁ ≫ b₂) ≫ b₂' ≫ b₁' := by rw [hL]
      _ = cL ≫ b₁ ≫ (b₂ ≫ b₂') ≫ b₁' := by simp only [Category.assoc]
      _ = cL ≫ b₁ ≫ b₁' := by rw [hb2, Category.id_comp]
      _ = cL := by rw [hb1, Category.comp_id]
  rw [← reassoc_of% hT, reassoc_of% hα, hq]

/-- The inverse of the composition comparison at `DerivedCategory.Qh.obj M`, followed by the
factorization of the composite, is the two factorizations of the factors composed. -/
private theorem compIso_inv_app_comp_factorsh (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv.app
          (DerivedCategory.Qh.obj M) ≫ (F ⋙ G).mapDerivedCategoryFactorsh.hom.app M =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app M) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) := by
  have hid : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app M) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have h := mapDerivedCategoryCompIso_hom_app F G (F ⋙ G) (Iso.refl _) M
  rw [mapDerivedCategoryCompIso_refl_eq, Iso.symm_hom, hid] at h
  exact h.trans (congrArg
    (G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app M) ≫ ·)
    (Category.comp_id _))

/-- **The derived 2-square on the image of `DerivedCategory.Qh`.**  The analogue over
`DerivedCategory.Qh` of `CategoryTheory.TwoSquare.mapDerivedCategory_app_Q`, with the four
canonical factorizations `CategoryTheory.Functor.mapDerivedCategoryFactorsh` moved to the side
they belong on: the derived 2-square at `DerivedCategory.Qh.obj M` is the degreewise 2-cell on
the homotopy category, localized, read across those four factorizations.

The two composition comparisons are computed by
`Stacks.Homology.mapDerivedCategoryCompIso_hom_app` once
`Stacks.Homology.mapDerivedCategoryCompIso_refl_eq` has identified them with the ones
`CategoryTheory.TwoSquare.mapDerivedCategory` is built from, and the middle factor by
`CategoryTheory.NatTrans.mapDerivedCategory_factorsh_hom`. -/
theorem _root_.CategoryTheory.TwoSquare.mapDerivedCategory_app_Qh
    (T : A ⥤ B) (L : A ⥤ C) (R : B ⥤ E) (Bo : C ⥤ E)
    [T.Additive] [L.Additive] [R.Additive] [Bo.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits Bo] [PreservesFiniteColimits Bo]
    (α : CategoryTheory.TwoSquare T L R Bo)
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    α.mapDerivedCategory.app (DerivedCategory.Qh.obj M) =
      R.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.hom.app M) ≫
        R.mapDerivedCategoryFactorsh.hom.app
            ((T.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
          DerivedCategory.Qh.map
              ((NatTrans.mapHomotopyCategory α.natTrans (ComplexShape.up ℤ)).app M) ≫
            Bo.mapDerivedCategoryFactorsh.inv.app
                ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
              Bo.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.inv.app M) := by
  have hb1 : Bo.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app M) ≫
      Bo.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.inv.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact Bo.mapDerivedCategory.map_id _
  show (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso T R).inv.app _ ≫
      (NatTrans.mapDerivedCategory α.natTrans).app _ ≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso L Bo).hom.app _ = _
  exact qh_chase _ _ _ _ _ _ _ _ _ _ _ _ _ (compIso_inv_app_comp_factorsh T R M)
    (NatTrans.mapDerivedCategory_factorsh_hom α.natTrans M) (compIso_inv_app_comp_factorsh L Bo M)
    ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso L Bo).hom_inv_id_app _)
    (Bo.mapDerivedCategoryFactorsh.hom_inv_id_app _) hb1

end TwoSquare

end Stacks.Homology

namespace CategoryTheory

universe v₅ v₆ v₇ v₈ u₅ u₆ u₇ u₈

variable {A : Type u₅} {B : Type u₆} {C : Type u₇} {D : Type u₈}
  [Category.{v₅} A] [Category.{v₆} B] [Category.{v₇} C] [Category.{v₈} D]
  {G G' : A ⥤ C} {H H' : B ⥤ D}
  {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}

/-- **The mate of a 2-square read at all six functors replaced by isomorphic ones.**  The two
adjunctions are transported along isomorphisms `e₁ : L₁ ≅ L₁'`, `e₂ : L₂ ≅ L₂'` of the left
adjoints and `d₁ : R₁ ≅ R₁'`, `d₂ : R₂ ≅ R₂'` of the right adjoints, and the two vertical edges
of the square along `eG : G ≅ G'` and `eH : H ≅ H'`; if the new 2-cell `α₂` is the old one
conjugated by those four of the isomorphisms it meets, then its mate is the old mate conjugated
by the remaining ones.

This is the three statements of
`StacksFrontier/CategoryTheory/Adjunction/MateTransport.lean` applied in turn, with the two
intermediate 2-cells — the vertically transported square and the vertically transported mate —
written out as composites of whiskerings, which is what makes their componentwise descriptions
hold by `rfl`. -/
theorem mateEquiv_transport_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (d₁ : R₁ ≅ R₁') (d₂ : R₂ ≅ R₂')
    (eG : G ≅ G') (eH : H ≅ H') (α : TwoSquare G L₁ L₂ H) (α₂ : TwoSquare G' L₁' L₂' H')
    (hα₂ : ∀ a : A, α₂.app a = e₂.inv.app (G'.obj a) ≫ L₂.map (eG.inv.app a) ≫ α.app a ≫
      eH.hom.app (L₁.obj a) ≫ H'.map (e₁.hom.app a))
    (Y : B) :
    (mateEquiv ((adj₁.ofNatIsoLeft e₁).ofNatIsoRight d₁)
          ((adj₂.ofNatIsoLeft e₂).ofNatIsoRight d₂) α₂).app Y =
      G'.map (d₁.inv.app Y) ≫ eG.inv.app (R₁.obj Y) ≫ (mateEquiv adj₁ adj₂ α).app Y ≫
        R₂.map (eH.hom.app Y) ≫ d₂.hom.app (H'.obj Y) := by
  have hleft : mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α₂ =
      mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _
        (Functor.whiskerRight eG.inv L₂ ≫ α.natTrans ≫ Functor.whiskerLeft L₁ eH.hom)) :=
    mateEquiv_ofNatIsoLeft adj₁ adj₂ e₁ e₂ _ α₂ fun a => by
      rw [hα₂]; simp only [TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Category.assoc]
  have hcv : TwoSquare.mk _ _ _ _ (Functor.whiskerLeft R₁ eG.inv ≫
        (mateEquiv adj₁ adj₂ α).natTrans ≫ Functor.whiskerRight eH.hom R₂) =
      mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _
        (Functor.whiskerRight eG.inv L₂ ≫ α.natTrans ≫ Functor.whiskerLeft L₁ eH.hom)) :=
    mateEquiv_conj_vertical adj₁ adj₂ eG eH α _ (fun _ => rfl) _ fun _ => rfl
  have hright := mateEquiv_ofNatIsoRight (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) d₁ d₂ α₂
    (TwoSquare.mk _ _ _ _ (Functor.whiskerRight d₁.inv G' ≫
      (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α₂).natTrans ≫
        Functor.whiskerLeft H' d₂.hom)) fun _ => rfl
  rw [← hright, hleft, ← hcv]
  simp only [TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]

end CategoryTheory

namespace Stacks.Cohomology

universe u

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance 10000] HasDerivedCategory.standard

/-- The chase behind `Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare_app`: one naturality
square turns the identification at the bottom edge around, and the two identifications at the top
edge are cancelled.  Stated at an arbitrary category with the objects implicit and the morphisms
explicit, so that it applies by `exact`. -/
private theorem conj_chase {D : Type*} [Category D] {o₁ o₂ o₃ o₄ o₅ o₆ o₇ : D}
    (x : o₁ ⟶ o₂) (p : o₂ ⟶ o₃) (q : o₃ ⟶ o₄) (u : o₁ ⟶ o₅) (u' : o₅ ⟶ o₁)
    (s : o₅ ⟶ o₆) (s' : o₆ ⟶ o₅) (t : o₆ ⟶ o₄) (q' : o₂ ⟶ o₇) (p' : o₇ ⟶ o₄)
    (hI : x ≫ p ≫ q = u ≫ s ≫ t) (hnat : p ≫ q = q' ≫ p')
    (hu : u' ≫ u = 𝟙 o₅) (hs : s' ≫ s = 𝟙 o₆) :
    t = s' ≫ u' ≫ x ≫ q' ≫ p' := by
  rw [← hnat, hI, reassoc_of% hu, reassoc_of% hs]

variable {X Y U V : RingedSpace.{u, u}} (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
  [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)]
  [PreservesFiniteLimits (modulePullback i)] [PreservesFiniteColimits (modulePullback i)]
  [PreservesFiniteLimits (modulePullback j)] [PreservesFiniteColimits (modulePullback j)]
  [PreservesFiniteLimits (modulePullback g)] [PreservesFiniteColimits (modulePullback g)]

/-- **The derived image of the comparison of iterated pullbacks is the derived 2-square of that
comparison.**  `Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare` is built from
`Stacks.Homology.mapDerivedCategoryTwoSquareOfIso`, and this is
`Stacks.Homology.mapDerivedCategoryTwoSquareOfIso_eq` at
`Stacks.Cohomology.pullbackCompIso`, whose `hom` is the transformation of
`Stacks.Cohomology.pullbackCompSquare`. -/
theorem mapDerivedCategoryPullbackCompSquare_eq (w : i ≫ f = g ≫ j) :
    mapDerivedCategoryPullbackCompSquare f i j g w =
      CategoryTheory.TwoSquare.mapDerivedCategory (pullbackCompSquare f i j g w) :=
  Stacks.Homology.mapDerivedCategoryTwoSquareOfIso_eq (modulePullback j) (modulePullback f)
    (modulePullback g) (modulePullback i) (pullbackCompIso f i j g w)

/-- **The derived 2-square of the comparison of iterated pullbacks, at an object, as the derived
base change square of [Stacks, Tag 08HY] conjugated by the four identifications `L?^* ≅ D(?^*)`.**

This is `Stacks.Cohomology.derivedPullbackSquare_eq_mapDerivedCategory` read at an object and
rearranged into the componentwise shape that
`CategoryTheory.mateEquiv_transport_app` asks of its transported 2-cell: the two identifications
at the top edge `Lj^*`, `Lg^*` moved to the other side, and the one at the bottom edge `Li^*`
turned around by naturality against the one at `Lf^*`. -/
theorem mapDerivedCategoryPullbackCompSquare_app (w : i ≫ f = g ≫ j)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (CategoryTheory.TwoSquare.mapDerivedCategory (pullbackCompSquare f i j g w)).app N =
      (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).inv.app
            ((modulePullback j).mapDerivedCategory.obj N) ≫
          (derivedPullback g).map
            ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).inv.app N) ≫
        (DerivedBaseChange.derivedPullbackSquare i g f j w).app N ≫
          (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).hom.app
              ((derivedPullback f).obj N) ≫
            (modulePullback i).mapDerivedCategory.map
              ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom.app N) := by
  have hI : (DerivedBaseChange.derivedPullbackSquare i g f j w).app N ≫
        (derivedPullback i).map
          ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom.app N) ≫
          (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).hom.app
            ((modulePullback f).mapDerivedCategory.obj N) =
      (derivedPullback g).map
          ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).hom.app N) ≫
        (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).hom.app
            ((modulePullback j).mapDerivedCategory.obj N) ≫
          (CategoryTheory.TwoSquare.mapDerivedCategory (pullbackCompSquare f i j g w)).app N := by
    rw [← mapDerivedCategoryPullbackCompSquare_eq]
    exact NatTrans.congr_app (derivedPullbackSquare_eq_mapDerivedCategory f i j g w) N
  have hu : (derivedPullback g).map
        ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).inv.app N) ≫
      (derivedPullback g).map
        ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).hom.app N) =
      𝟙 ((derivedPullback g).obj ((modulePullback j).mapDerivedCategory.obj N)) := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact (derivedPullback g).map_id _
  exact conj_chase _ _ _ _ _ _ _ _ _ _ hI
    ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).hom.naturality _) hu
    ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).inv_hom_id_app _)

end Stacks.Cohomology

namespace Stacks.Cohomology.SupportedComplexes

universe u

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.openImmersionModulePullback_preservesHomology
attribute [local instance] preservesFiniteLimits_modulePullback_of_isOpenImmersion
attribute [local instance] RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback
attribute [local instance] preservesFiniteLimits_modulePullback_closedSubsetInclusion

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-- `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare_eq_mateEquiv` at an object:
the base-change map of [Stacks, Tag 08HY] for the restriction square is a component of that
mate. -/
theorem supportedPullbackBaseChangeMap_eq_mateEquiv_app
    (N : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    supportedPullbackBaseChangeMap f Z N =
      (mateEquiv (derivedAdjunction (closedSubsetInclusion X Z))
        (derivedAdjunction (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
        (DerivedBaseChange.derivedPullbackSquare (closedSubsetRestriction f Z)
          (closedSubsetInclusion X' (closedSubsetPreimage f Z)) (closedSubsetInclusion X Z) f
          (closedSubsetRestriction_comp_closedSubsetInclusion f Z))).app N :=
  congrArg (fun t : CategoryTheory.TwoSquare
      (derivedPushforward (closedSubsetInclusion X Z))
      (derivedPullback (closedSubsetRestriction f Z)) (derivedPullback f)
      (derivedPushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))) => t.app N)
    (DerivedBaseChange.derivedBaseChangeSquare_eq_mateEquiv (closedSubsetRestriction f Z)
      (closedSubsetInclusion X' (closedSubsetPreimage f Z)) (closedSubsetInclusion X Z) f
      (closedSubsetRestriction_comp_closedSubsetInclusion f Z))

/-- **The derived base change of [Stacks, Tag 08HY] for the restriction square, conjugated by
the six identifications of the derived functors with the degreewise ones.**

This is `CategoryTheory.mateEquiv_transport_app` at the two derived adjunctions of
[Stacks, Tag 079W] along `i` and `i'`, whose hypothesis on the transported 2-cell is
`Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare_app`. -/
theorem mateEquiv_mapDerivedCategoryPullbackCompSquare_app
    (hZ : IsClosed Z) (hZ' : IsClosed (closedSubsetPreimage f Z))
    (N : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
    (mateEquiv
        (((derivedAdjunction (closedSubsetInclusion X Z)).ofNatIsoLeft
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory
              (closedSubsetInclusion X Z))).ofNatIsoRight
          (derivedPushforwardComparisonIso (closedSubsetInclusion X Z)).symm)
        (((derivedAdjunction
              (closedSubsetInclusion X' (closedSubsetPreimage f Z))).ofNatIsoLeft
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory
              (closedSubsetInclusion X' (closedSubsetPreimage f Z)))).ofNatIsoRight
          (derivedPushforwardComparisonIso
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).symm)
        (CategoryTheory.TwoSquare.mapDerivedCategory
          (pullbackCompSquare (closedSubsetInclusion X Z) (closedSubsetRestriction f Z) f
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))
            (closedSubsetRestriction_comp_closedSubsetInclusion f Z)))).app N =
      (modulePullback f).mapDerivedCategory.map
            ((closedPushforwardComparison X Z).hom.app N) ≫
          (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).inv.app
            ((derivedPushforward (closedSubsetInclusion X Z)).obj N) ≫
        (mateEquiv (derivedAdjunction (closedSubsetInclusion X Z))
            (derivedAdjunction (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
            (DerivedBaseChange.derivedPullbackSquare (closedSubsetRestriction f Z)
              (closedSubsetInclusion X' (closedSubsetPreimage f Z))
              (closedSubsetInclusion X Z) f
              (closedSubsetRestriction_comp_closedSubsetInclusion f Z))).app N ≫
          (derivedPushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
              ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory
                (closedSubsetRestriction f Z)).hom.app N) ≫
            (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app
              ((modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory.obj N) :=
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
  CategoryTheory.mateEquiv_transport_app (derivedAdjunction (closedSubsetInclusion X Z))
    (derivedAdjunction (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory (closedSubsetInclusion X Z))
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory
      (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
    (derivedPushforwardComparisonIso (closedSubsetInclusion X Z)).symm
    (derivedPushforwardComparisonIso
      (closedSubsetInclusion X' (closedSubsetPreimage f Z))).symm
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f)
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory (closedSubsetRestriction f Z))
    (DerivedBaseChange.derivedPullbackSquare (closedSubsetRestriction f Z)
      (closedSubsetInclusion X' (closedSubsetPreimage f Z)) (closedSubsetInclusion X Z) f
      (closedSubsetRestriction_comp_closedSubsetInclusion f Z)) _
    (mapDerivedCategoryPullbackCompSquare_app (closedSubsetInclusion X Z)
      (closedSubsetRestriction f Z) f (closedSubsetInclusion X' (closedSubsetPreimage f Z))
      (closedSubsetRestriction_comp_closedSubsetInclusion f Z)) N

/-- **The derived image of the underived base change of the restriction square is the transported
mate of the derived comparison of iterated derived pullbacks.**

This is `mateEquiv_derivedAdjunction_eq_mapDerivedCategory` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`
at `i`, `i'`, `f` and `f|_{Z'}`, with its right-hand side rewritten by
`Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso_hom_eq_mateEquiv`,
which exhibits the underived base change as the mate of the comparison of the two iterated
pullbacks. -/
theorem closedSubsetPushforwardPullbackNatIso_mapDerivedCategory_app_eq
    (hZ : IsClosed Z) (hZ' : IsClosed (closedSubsetPreimage f Z))
    (N : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
    (CategoryTheory.TwoSquare.mapDerivedCategory (CategoryTheory.TwoSquare.mk _ _ _ _
          (closedSubsetPushforwardPullbackNatIso f Z).hom)).app N =
      (mateEquiv
        (((derivedAdjunction (closedSubsetInclusion X Z)).ofNatIsoLeft
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory
              (closedSubsetInclusion X Z))).ofNatIsoRight
          (derivedPushforwardComparisonIso (closedSubsetInclusion X Z)).symm)
        (((derivedAdjunction
              (closedSubsetInclusion X' (closedSubsetPreimage f Z))).ofNatIsoLeft
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory
              (closedSubsetInclusion X' (closedSubsetPreimage f Z)))).ofNatIsoRight
          (derivedPushforwardComparisonIso
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).symm)
        (CategoryTheory.TwoSquare.mapDerivedCategory
          (pullbackCompSquare (closedSubsetInclusion X Z) (closedSubsetRestriction f Z) f
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))
            (closedSubsetRestriction_comp_closedSubsetInclusion f Z)))).app N := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
  have h2 := mateEquiv_derivedAdjunction_eq_mapDerivedCategory
    (closedSubsetInclusion X' (closedSubsetPreimage f Z)) (closedSubsetInclusion X Z) f
    (closedSubsetRestriction f Z)
    (pullbackCompSquare (closedSubsetInclusion X Z) (closedSubsetRestriction f Z) f
      (closedSubsetInclusion X' (closedSubsetPreimage f Z))
      (closedSubsetRestriction_comp_closedSubsetInclusion f Z))
  have h2' : mateEquiv (modulePullbackPushforwardAdjunction (closedSubsetInclusion X Z))
        (modulePullbackPushforwardAdjunction
          (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
        (pullbackCompSquare (closedSubsetInclusion X Z) (closedSubsetRestriction f Z) f
          (closedSubsetInclusion X' (closedSubsetPreimage f Z))
          (closedSubsetRestriction_comp_closedSubsetInclusion f Z)) =
      (closedSubsetPushforwardPullbackNatIso f Z).hom :=
    (closedSubsetPushforwardPullbackNatIso_hom_eq_mateEquiv f Z).symm
  exact (congrArg (fun β : CategoryTheory.TwoSquare
      (modulePushforward (closedSubsetInclusion X Z))
      (modulePullback (closedSubsetRestriction f Z)) (modulePullback f)
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))) =>
    (CategoryTheory.TwoSquare.mapDerivedCategory β).app N) h2'.symm).trans
      (NatTrans.congr_app h2.symm N)

/-- The chase behind
`Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mapDerivedCategory`: the
identification `Lf^* ≅ D(f^*)` is moved across the comparison `D(i_*) ≅ Ri_*` by naturality and
cancelled, and the identification `Lr^* ≅ D(r^*)` likewise across `Ri'_* ≅ D(i'_*)`.  Stated at
an arbitrary category with the objects implicit and the morphisms explicit, so that it applies by
`exact`. -/
private theorem final_chase {D : Type*} [Category D] {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : D}
    (bX : a₁ ⟶ a₂) (bT : a₂ ⟶ a₃) (m : a₃ ⟶ a₄) (c₀ : a₁ ⟶ b₁) (bXh : b₁ ⟶ b₂)
    (c : a₂ ⟶ b₂) (e : b₂ ⟶ b₁) (x x' : b₁ ⟶ b₃) (k : b₃ ⟶ b₄) (l : b₄ ⟶ a₃)
    (l₀ : b₃ ⟶ a₄) (k' : a₄ ⟶ a₃)
    (hT : bT = c ≫ e ≫ x' ≫ k ≫ l) (hb : x = x') (hnatf : bX ≫ c = c₀ ≫ bXh)
    (hxe : bXh ≫ e = 𝟙 b₁) (hnatr : k ≫ l = l₀ ≫ k') (hk : k' ≫ m = 𝟙 a₄) :
    c₀ ≫ x ≫ l₀ = bX ≫ bT ≫ m := by
  calc c₀ ≫ x ≫ l₀ = c₀ ≫ x' ≫ l₀ := by rw [hb]
    _ = c₀ ≫ (bXh ≫ e) ≫ x' ≫ l₀ ≫ k' ≫ m := by
        rw [hxe, hk, Category.id_comp, Category.comp_id]
    _ = (c₀ ≫ bXh) ≫ e ≫ x' ≫ (l₀ ≫ k') ≫ m := by simp only [Category.assoc]
    _ = (bX ≫ c) ≫ e ≫ x' ≫ (k ≫ l) ≫ m := by rw [hnatf, hnatr]
    _ = bX ≫ (c ≫ e ≫ x' ≫ k ≫ l) ≫ m := by simp only [Category.assoc]
    _ = bX ≫ bT ≫ m := by rw [hT]

/-- **The derived base change map of [Stacks, Tag 08HY] for the Cartesian square of the
restriction of an open immersion to a closed subset is the derived image of the underived base
change map.**

The left-hand side is the composite
`Lf^*(i_*N) ≅ Lf^*(Ri_*N) --bc--> Ri'_*(Lr^*N) ≅ i'_*(Lr^*N)`, the right-hand side the same map
read through `Lf^* ≅ D(f^*)`, `Lr^* ≅ D(r^*)` and the derived image
`CategoryTheory.TwoSquare.mapDerivedCategory` of the underived base change
`closedSubsetPushforwardPullbackNatIso`.

Both pushforwards are exact, `Z` and `f⁻¹(Z)` being closed, which is what `hZ` and `hZ'` are
for; both pullbacks along `f` and `f|_{Z'}` are exact, those being open immersions; and both
pullbacks along `i` and `i'` are exact unconditionally. -/
theorem supportedPullbackBaseChangeMap_eq_mapDerivedCategory
    (hZ : IsClosed Z) (hZ' : IsClosed (closedSubsetPreimage f Z))
    (N : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
    (derivedPullback f).map ((closedPushforwardComparison X Z).hom.app N) ≫
          supportedPullbackBaseChangeMap f Z N ≫
          (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app
            ((derivedPullback (closedSubsetRestriction f Z)).obj N) =
      (DerivedOpenImmersion.derivedPullbackOpenImmersionIso f).hom.app
            ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj N) ≫
          (CategoryTheory.TwoSquare.mapDerivedCategory (CategoryTheory.TwoSquare.mk _ _ _ _
            (closedSubsetPushforwardPullbackNatIso f Z).hom)).app N ≫
          (modulePushforward
              (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
            ((DerivedOpenImmersion.derivedPullbackOpenImmersionIso
              (closedSubsetRestriction f Z)).inv.app N) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
  refine final_chase _ _ _ _ _ _ _ _ _ _ _ _ _
    ((closedSubsetPushforwardPullbackNatIso_mapDerivedCategory_app_eq f Z hZ hZ' N).trans
      (mateEquiv_mapDerivedCategoryPullbackCompSquare_app f Z hZ hZ' N))
    (supportedPullbackBaseChangeMap_eq_mateEquiv_app f Z N)
    (((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom.naturality
      ((closedPushforwardComparison X Z).hom.app N)).symm)
    ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom_inv_id_app _)
    ((closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.naturality _) ?_
  rw [← Functor.map_comp]
  exact (congrArg (modulePushforward
        (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
      ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory
        (closedSubsetRestriction f Z)).hom_inv_id_app N)).trans
    ((modulePushforward
      (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map_id _)

/-- The chase behind
`Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mapDerivedCategory_Qh`:
the identification `Lf^* ≅ D(f^*)` is carried across the factorization of `D(i_*)` by naturality
and then absorbed into the comparison of the derived pullback, and the two maps of `D(i'_*)` at
the other end are merged.  Stated at an arbitrary category with the objects implicit and the
morphisms explicit, so that it applies by `exact`. -/
private theorem qh_final_chase {D : Type*} [Category D] {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ : D}
    (lhs : o₁ ⟶ o₄) (bX : o₁ ⟶ o₂) (bT : o₂ ⟶ o₃) (mm : o₃ ⟶ o₄)
    (a : o₂ ⟶ o₅) (b : o₅ ⟶ o₆) (q : o₆ ⟶ o₇) (d : o₇ ⟶ o₈) (e : o₈ ⟶ o₃)
    (c₀ : o₁ ⟶ o₉) (bX' : o₉ ⟶ o₅) (cmp : o₉ ⟶ o₆) (me : o₈ ⟶ o₄)
    (h1 : lhs = bX ≫ bT ≫ mm) (h2 : bT = a ≫ b ≫ q ≫ d ≫ e)
    (h3 : bX ≫ a = c₀ ≫ bX') (h4 : bX' ≫ b = cmp) (h5 : e ≫ mm = me) :
    lhs = c₀ ≫ cmp ≫ q ≫ d ≫ me := by
  rw [h1, h2]
  calc bX ≫ (a ≫ b ≫ q ≫ d ≫ e) ≫ mm
      = (bX ≫ a) ≫ b ≫ q ≫ d ≫ e ≫ mm := by simp only [Category.assoc]
    _ = (c₀ ≫ bX') ≫ b ≫ q ≫ d ≫ me := by rw [h3, h5]
    _ = c₀ ≫ (bX' ≫ b) ≫ q ≫ d ≫ me := by simp only [Category.assoc]
    _ = c₀ ≫ cmp ≫ q ≫ d ≫ me := by rw [h4]

/-- **The derived base change map of [Stacks, Tag 08HY] for the restriction square, on the image
of `DerivedCategory.Qh`.**  The equation of
`Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mapDerivedCategory` at
`N = DerivedCategory.Qh.obj M₁`, with the right-hand side written out on the homotopy category:
the four canonical factorizations
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, the comparison
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison` of the derived
pullback along `f`, and the `DerivedCategory.Qh`-image of the underived base change
`closedSubsetPushforwardPullbackNatIso` read on homotopy categories.

The `Qh`-component formula for the derived 2-square is
`CategoryTheory.TwoSquare.mapDerivedCategory_app_Qh`. -/
theorem supportedPullbackBaseChangeMap_eq_mapDerivedCategory_Qh
    (hZ : IsClosed Z) (hZ' : IsClosed (closedSubsetPreimage f Z))
    (M₁ : HomotopyCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))) (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
    (derivedPullback f).map
            ((closedPushforwardComparison X Z).hom.app (DerivedCategory.Qh.obj M₁)) ≫
          supportedPullbackBaseChangeMap f Z (DerivedCategory.Qh.obj M₁) ≫
          (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app
            ((derivedPullback (closedSubsetRestriction f Z)).obj
              (DerivedCategory.Qh.obj M₁)) =
      (derivedPullback f).map
            ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategoryFactorsh.hom.app
              M₁) ≫
          (derivedPullbackComparison f).app
            (((modulePushforward (closedSubsetInclusion X Z)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj M₁) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
            (closedSubsetPushforwardPullbackNatIso f Z).hom (ComplexShape.up ℤ)).app M₁) ≫
          (modulePushforward (closedSubsetInclusion X'
                (closedSubsetPreimage f Z))).mapDerivedCategoryFactorsh.inv.app
              (((modulePullback (closedSubsetRestriction f Z)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj M₁) ≫
            (modulePushforward (closedSubsetInclusion X'
                (closedSubsetPreimage f Z))).mapDerivedCategory.map
              ((modulePullback
                  (closedSubsetRestriction f Z)).mapDerivedCategoryFactorsh.inv.app M₁ ≫
                (DerivedOpenImmersion.derivedPullbackOpenImmersionIso
                  (closedSubsetRestriction f Z)).inv.app (DerivedCategory.Qh.obj M₁)) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
  exact qh_final_chase _ _ _ _ _ _ _ _ _ _ _ _ _
    (supportedPullbackBaseChangeMap_eq_mapDerivedCategory f Z hZ hZ'
      (DerivedCategory.Qh.obj M₁))
    (CategoryTheory.TwoSquare.mapDerivedCategory_app_Qh
      (modulePushforward (closedSubsetInclusion X Z))
      (modulePullback (closedSubsetRestriction f Z)) (modulePullback f)
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
      (CategoryTheory.TwoSquare.mk _ _ _ _
        (closedSubsetPushforwardPullbackNatIso f Z).hom) M₁)
    (((DerivedOpenImmersion.derivedPullbackOpenImmersionIso f).hom.naturality
      ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategoryFactorsh.hom.app
        M₁)).symm)
    (Stacks.Homology.leftDerivedIsoMapDerivedCategory_hom_app (modulePullback f)
      (derivedPullback f) (derivedPullbackComparison f) _)
    (((modulePushforward (closedSubsetInclusion X'
      (closedSubsetPreimage f Z))).mapDerivedCategory.map_comp _ _).symm)

end Stacks.Cohomology.SupportedComplexes

end
