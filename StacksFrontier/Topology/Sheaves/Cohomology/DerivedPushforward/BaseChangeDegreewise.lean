module

public import StacksFrontier.CategoryTheory.Adjunction.MateTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeSquareDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactAdjunctionDegreewise

/-!
# The derived base change of a square of ringed spaces is the derived image of the underived one

Let

```
  U --- i ---> X
  |            |
  g            f
  |            |
  V --- j ---> Y
```

be a commutative square of ringed spaces, `w : i ≫ f = g ≫ j`, along whose four morphisms
pullback of sheaves of modules is exact and along whose two horizontal morphisms pushforward is
right exact.  Two base change maps sit over the square.  Underived,
`Stacks.Cohomology.pushforwardRestrictMap` is the canonical map `f_* ⋙ j^* ⟶ i^* ⋙ g_*`, which
by `Stacks.Cohomology.pushforwardRestrictMap_eq_mateEquiv` is the mate, under `f^* ⊣ f_*` and
`g^* ⊣ g_*`, of the comparison `Stacks.Cohomology.pullbackCompSquare` of the two iterated
underived pullbacks.  Derived, `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare` of
[Stacks, Tag 08HY] is the mate, under the derived adjunctions `Lf^* ⊣ Rf_*` and `Lg^* ⊣ Rg_*` of
[Stacks, Tag 079W], of the comparison
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare` of the two iterated *derived*
pullbacks.

**The main result of this file is that the second is the derived image of the first**: under the
four identifications `L?^* ≅ D(?^*)` of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory` and the two
identifications `D(?_*) ≅ R?_*` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardComparisonIso`, the derived
base change map of [Stacks, Tag 08HY] **is** `CategoryTheory.TwoSquare.mapDerivedCategory` of the
underived base change map.  This is the capstone of the degreewise half of Stacks tag 0G87.

## Main results

* `CategoryTheory.NatTrans.mapDerivedCategory_app_Qh`: the defining formula for
  `CategoryTheory.NatTrans.mapDerivedCategory` on the image of `DerivedCategory.Qh`.
* `Stacks.Homology.mapDerivedCategoryIsoOfIso_hom`: **the degreewise change of functor is the
  derived form of the transformation.**  The isomorphism of induced functors that an isomorphism
  of exact functors gives is `CategoryTheory.NatTrans.mapDerivedCategory` of its `hom`.
* `Stacks.Homology.mapDerivedCategoryTwoSquareOfIso_eq_mapDerivedCategory`: **the two
  constructions of the derived image of a 2-square agree.**
* `CategoryTheory.mateEquiv_conj`: **conjugating all six functors of a square of adjunctions
  conjugates the mate.**  The three transports of
  `StacksFrontier/CategoryTheory/Adjunction/MateTransport.lean` composed into one statement.
* `Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare_eq_mapDerivedCategory`: the derived
  image of `Stacks.Cohomology.pullbackCompSquare` built in
  `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/BaseChangeSquareDegreewise.lean` is
  `CategoryTheory.TwoSquare.mapDerivedCategory` of it.
* `Stacks.Cohomology.derivedBaseChangeSquare_eq_mapDerivedCategory`: **the main result**, and
  `Stacks.Cohomology.derivedBaseChangeMap_eq_mapDerivedCategory`, its component form.

## Implementation notes

*How the four input pieces enter.*  `Stacks.Cohomology.pushforwardRestrictMap_eq_mateEquiv`
turns the underived base change map into a mate, which is what makes the mates calculus
applicable to it at all; `CategoryTheory.mateEquiv_mapDerivedCategory` is consumed through
`mateEquiv_derivedAdjunction_eq_mapDerivedCategory` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`, which is itself
`…ofNatIso_derivedAdjunction_eq_mapDerivedCategory` composed with it; and
`Stacks.Cohomology.derivedPullbackSquare_eq_mapDerivedCategory` supplies the comparison of the
two pullback squares.  All three are consumed in `Stacks.Cohomology.mateEquiv_transported_eq` and
`Stacks.Cohomology.conj_derivedPullbackSquare`.

*The third obstacle, and how it is removed.*  The mates statement consumes
`CategoryTheory.TwoSquare.mapDerivedCategory`, while
`Stacks.Cohomology.derivedPullbackSquare_eq_mapDerivedCategory` lands at
`Stacks.Homology.mapDerivedCategoryTwoSquareOfIso`.  Both are built from one comparison of the
derived functor of a composite with the composite of the derived functors — that is
`Stacks.Homology.mapDerivedCategoryCompIso_refl_eq` — but their middle factors were not
identified: one is `Stacks.Homology.mapDerivedCategoryIsoOfIso`, pinned by the universal property
of a left derived functor over `DerivedCategory.Qh`, and the other is
`CategoryTheory.NatTrans.mapDerivedCategory`, defined as a lift through `DerivedCategory.Q`.
`Stacks.Homology.mapDerivedCategoryIsoOfIso_hom` identifies them, by comparing both against the
structure map of the target over `DerivedCategory.Qh`:
`CategoryTheory.Functor.leftDerived_ext` reduces the equality to the image of `Qh`, where the
first is computed by its universal property and the second by
`CategoryTheory.NatTrans.mapDerivedCategory_app_Qh`.

*Why the derived transformation needed a `Qh`-level formula.*  `NatTrans.mapDerivedCategory` is a
lift through `DerivedCategory.Q`, so its value is given on cochain complexes;
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` crosses from there to the homotopy
category, and the only thing left is that the two degreewise factorizations
`CategoryTheory.Functor.mapHomotopyCategoryFactors` are identities.  Their source and target are
definitionally but not syntactically equal, so that identity cannot be *rewritten* in; it is
supplied as a `show`, which is checked at default transparency.

*The shape of the main statement, and why.*  It is an equality of natural transformations with
the comparisons whiskered onto both sides —
`bc ≫ whiskerRight _ _ ≫ whiskerLeft _ _ = whiskerRight _ _ ≫ whiskerLeft _ _ ≫ D(bc)` — rather
than an equality of 2-squares at the degreewise functors.  That is the shape
`Stacks.Cohomology.derivedPullbackSquare_eq_mapDerivedCategory` already has, so the two compose
without a conversion; and it needs no new definition of a conjugated 2-square, which would be a
seventh name for data the file already has.  The left-hand factor of each composite is changed
first, so that both sides read "replace the outer functor, then the inner one".

*Why the mate transport is hoisted.*  Instantiating
`CategoryTheory.mateEquiv_ofNatIsoLeft`, `…mateEquiv_conj_vertical` and `…mateEquiv_ofNatIsoRight`
one after another at the canonical derived functors exhausts the kernel's budget: the
intermediate 2-squares have to be written out at those types three times over.  They are composed
once and for all at variable categories in `CategoryTheory.mateEquiv_conj`, and the canonical
result is one application of it.  For the same reason the chain of three rewrites that identifies
the transported mate with the derived image of the underived map is a separate declaration,
`Stacks.Cohomology.mateEquiv_transported_eq`: performed inside the main theorem, each rewrite has
to re-check a motive carrying the whiskerings of the statement, and that is what times out.

*The two isomorphisms of pushforwards are oriented as the development states them.*
`CategoryTheory.mateEquiv_conj` takes the comparisons of the right adjoints as `R' ≅ R`, which is
the direction of `…derivedPushforwardComparisonIso`, so the transported adjunction it produces is
spelled `…ofNatIsoRight (derivedPushforwardComparisonIso _).symm` — syntactically the spelling in
`…mateEquiv_derivedAdjunction_eq_mapDerivedCategory`.  With the opposite convention the two
differ by one projection of `CategoryTheory.Iso.symm` at every occurrence, and the rewrite has to
reconcile them inside the derived-functor terms.

*No `@[stacks]` attribute.*  This is one component of Stacks tag 0G87, not the whole tag, and the
derived base change map it is about already carries `@[stacks 08HY]` at
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`.

## References

* [Stacks Project, Remark 20.28.3 (Tag 08HY)](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Lemma 20.28.6 (Tag 079W)](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Lemma 20.28.6 (Tag 08FE)](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Section 17.6 (Tag 0096)](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The derived form of a natural transformation of exact functors on the image of
`DerivedCategory.Qh`.**  Composed with the structure map of the target it is the structure map of
the source followed by the degreewise transformation on the homotopy category.  This is the form
`CategoryTheory.Functor.leftDerived_ext` consumes, the derived transformation being pinned by it
as a map into the left derived functor `D(G)`. -/
theorem NatTrans.mapDerivedCategory_app_Qh (η : F ⟶ G)
    (M : HomotopyCategory C (ComplexShape.up ℤ)) :
    (NatTrans.mapDerivedCategory η).app (DerivedCategory.Qh.obj M) ≫
        G.mapDerivedCategoryFactorsh.hom.app M =
      F.mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app M) := by
  obtain ⟨K⟩ := M
  show (NatTrans.mapDerivedCategory η).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
    F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, Functor.mapDerivedCategoryFactorsh_hom_app,
    NatTrans.mapDerivedCategory_app_comp_assoc, Iso.inv_hom_id_app_assoc]
  have hsq0 : (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K ≫
        (NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) ≫
        (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K := by
    show 𝟙 _ ≫ (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  have hsq : DerivedCategory.Qh.map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K)) ≫
        DerivedCategory.Qh.map
          ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) := by
    rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp, hsq0]
  have hsq2 : ((DerivedCategory.quotientCompQhIso D).inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K)) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) ≫
        (DerivedCategory.quotientCompQhIso D).inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) := by
    rw [Category.assoc, hsq, ← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  rw [Category.assoc, Category.assoc, hsq2]

section MateConj

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G G' : A ⥤ C} {H H' : B ⥤ D}
  {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}

/-- The chase that remains once the counit equation has been used: a pair of mutually inverse
morphisms in the image of a functor, one naturality square, and a second pair of mutually inverse
morphisms.  Stated at an arbitrary category with the objects implicit and the morphisms explicit,
so that it applies by `exact` at the two places it is needed. -/
private theorem conj_chase {𝒳 : Type*} [Category* 𝒳] {P Q P' Q' W : 𝒳}
    (u : Q ⟶ P) (u' : P ⟶ Q) (x : P ⟶ P') (y : P' ⟶ Q') (z : Q' ⟶ Q) (z' : Q ⟶ Q')
    (t : Q ⟶ W) (hu : u ≫ u' = CategoryStruct.id Q) (hz : z' ≫ z = CategoryStruct.id Q)
    (hnat : u' ≫ z' = x ≫ y) :
    u ≫ x ≫ y ≫ z ≫ t = t := by
  rw [← Category.assoc x y, ← hnat, Category.assoc, ← Category.assoc u u', hu,
    Category.id_comp, ← Category.assoc z' z, hz, Category.id_comp]

/-- The one reassociation of a five-fold composite that the three transports need: the middle
three factors are the conjugated 2-cell, and the hypotheses of
`CategoryTheory.mateEquiv_conj_vertical` and `CategoryTheory.mateEquiv_ofNatIsoRight` are stated
with that bracketing while the hypothesis of `CategoryTheory.mateEquiv_conj` is flat. -/
private theorem assoc5 {𝒳 : Type*} [Category* 𝒳] {o₁ o₂ o₃ o₄ o₅ o₆ : 𝒳}
    (m : o₁ ⟶ o₂) (n : o₂ ⟶ o₃) (p : o₃ ⟶ o₄) (q : o₄ ⟶ o₅) (r : o₅ ⟶ o₆) :
    m ≫ n ≫ p ≫ q ≫ r = m ≫ (n ≫ p ≫ q) ≫ r := by
  simp only [Category.assoc]

/-- **Conjugating all six functors of a square of adjunctions conjugates the mate.**  The two
adjunctions are transported along isomorphisms `e₁ : L₁ ≅ L₁'` and `e₂ : L₂ ≅ L₂'` of their left
adjoints and `d₁ : R₁' ≅ R₁`, `d₂ : R₂' ≅ R₂` of their right adjoints, the two vertical edges are
replaced by `G'` and `H'` along `eG` and `eH`, and the 2-cell `α` is replaced by `α'` read at the
new edges: then the mate of `α'` is the mate of `α`, conjugated by `d₁` and `eG` at its source and
by `eH` and `d₂` at its target.

This is `CategoryTheory.mateEquiv_ofNatIsoLeft`, `CategoryTheory.mateEquiv_conj_vertical` and
`CategoryTheory.mateEquiv_ofNatIsoRight` composed.  The comparisons of the right adjoints point
from the new functor to the old one, which is the direction in which the application that this is
for — the derived base change of [Stacks, Tag 08HY] — has them. -/
theorem mateEquiv_conj (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (d₁ : R₁' ≅ R₁) (d₂ : R₂' ≅ R₂)
    (eG : G ≅ G') (eH : H ≅ H')
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁' L₂' H')
    (hα : ∀ a : A, α'.app a = L₂'.map (eG.inv.app a) ≫ e₂.inv.app (G.obj a) ≫ α.app a ≫
      H.map (e₁.hom.app a) ≫ eH.hom.app (L₁'.obj a)) :
    (mateEquiv adj₁ adj₂ α).natTrans ≫ Functor.whiskerRight eH.hom R₂ ≫
        Functor.whiskerLeft H' d₂.inv =
      Functor.whiskerRight d₁.inv G ≫ Functor.whiskerLeft R₁' eG.hom ≫
        (mateEquiv ((adj₁.ofNatIsoLeft e₁).ofNatIsoRight d₁.symm)
          ((adj₂.ofNatIsoLeft e₂).ofNatIsoRight d₂.symm) α').natTrans := by
  have hstep1 := mateEquiv_ofNatIsoLeft adj₁ adj₂ e₁ e₂ α
    (TwoSquare.mk _ _ _ _ (Functor.whiskerLeft G e₂.inv ≫ α.natTrans ≫
      Functor.whiskerRight e₁.hom H)) (fun a => rfl)
  have hstep2 := mateEquiv_conj_vertical (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) eG eH
    (TwoSquare.mk _ _ _ _ (Functor.whiskerLeft G e₂.inv ≫ α.natTrans ≫
      Functor.whiskerRight e₁.hom H)) α'
    (fun a => (hα a).trans (assoc5 _ _ _ _ _))
    (TwoSquare.mk _ _ _ _ (Functor.whiskerLeft R₁ eG.inv ≫ (mateEquiv adj₁ adj₂ α).natTrans ≫
      Functor.whiskerRight eH.hom R₂)) (fun Y => by rw [hstep1]; rfl)
  have hstep3 := mateEquiv_ofNatIsoRight (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂)
    d₁.symm d₂.symm α'
    (TwoSquare.mk _ _ _ _ (Functor.whiskerRight d₁.symm.inv G' ≫
      (Functor.whiskerLeft R₁ eG.inv ≫ (mateEquiv adj₁ adj₂ α).natTrans ≫
        Functor.whiskerRight eH.hom R₂) ≫ Functor.whiskerLeft H' d₂.symm.hom))
    (fun Y => by rw [← hstep2]; rfl)
  rw [← hstep3]
  ext Y
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  refine (conj_chase (G.map (d₁.inv.app Y)) (G.map (d₁.symm.inv.app Y))
    (eG.hom.app (R₁'.obj Y)) (G'.map (d₁.symm.inv.app Y)) (eG.inv.app (R₁.obj Y))
    (eG.hom.app (R₁.obj Y)) _ ?_ (eG.hom_inv_id_app (R₁.obj Y)) ?_).symm
  · rw [← G.map_comp]
    exact congrArg G.map (d₁.inv_hom_id_app Y) |>.trans (G.map_id _)
  · exact eG.hom.naturality (d₁.symm.inv.app Y)

end MateConj

end CategoryTheory

namespace Stacks.Homology

section ChangeOfFunctor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- **The universal property of `Stacks.Homology.mapDerivedCategoryIsoOfIso` with the twist moved
to the other side**, at an object of the homotopy category: the degreewise change of functor
appears as the transformation `e` read on the homotopy category, rather than as its inverse on the
other side of the equation. -/
theorem mapDerivedCategoryIsoOfIso_hom_app_Qh (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedCategoryIsoOfIso F G e).hom.app (DerivedCategory.Qh.obj M) ≫
        G.mapDerivedCategoryFactorsh.hom.app M =
      F.mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app M) := by
  have huniv := mapDerivedCategoryIsoOfIso_hom_app F G e M
  have hcomp : (mapDerivedCategoryComparisonOfIso F G e).hom.app M =
      G.mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app M) := rfl
  have hcancel : DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app M) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app M) = 𝟙 _ := by
    rw [← DerivedCategory.Qh.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id,
      NatTrans.id_app, DerivedCategory.Qh.map_id]
  rw [hcomp] at huniv
  rw [← huniv, Category.assoc, Category.assoc, hcancel]
  exact (congrArg ((mapDerivedCategoryIsoOfIso F G e).hom.app (DerivedCategory.Qh.obj M) ≫ ·)
    (Category.comp_id (G.mapDerivedCategoryFactorsh.hom.app M))).symm

/-- **The degreewise change of functor is the derived form of the transformation.**  The
isomorphism `D(F) ≅ D(G)` that an isomorphism `e : F ≅ G` of exact functors induces, built in
`Stacks.Homology.mapDerivedCategoryIsoOfIso` out of the universal property of a left derived
functor, has for its `hom` the lift `CategoryTheory.NatTrans.mapDerivedCategory e.hom` of the
degreewise transformation through `DerivedCategory.Q`.

Both are maps into the left derived functor `D(G)`, so they agree as soon as their composites with
its structure map do, and there each is computed: the first by
`Stacks.Homology.mapDerivedCategoryIsoOfIso_hom_app_Qh`, the second by
`CategoryTheory.NatTrans.mapDerivedCategory_app_Qh`. -/
theorem mapDerivedCategoryIsoOfIso_hom (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (mapDerivedCategoryIsoOfIso F G e).hom = NatTrans.mapDerivedCategory e.hom := by
  refine Functor.leftDerived_ext G.mapDerivedCategory G.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_
  ext M
  exact (mapDerivedCategoryIsoOfIso_hom_app_Qh F G e M).trans
    (NatTrans.mapDerivedCategory_app_Qh e.hom M).symm

end ChangeOfFunctor

section TwoSquare

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {E : Type u₄} [Category.{v₄} E] [Abelian E] [HasDerivedCategory.{w₄} E]
  (T : A ⥤ B) (L : A ⥤ C) (R : B ⥤ E) (Bo : C ⥤ E)
  [T.Additive] [L.Additive] [R.Additive] [Bo.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits Bo] [PreservesFiniteColimits Bo]

/-- **The two constructions of the derived image of a 2-square agree.**  For an invertible
2-cell, `Stacks.Homology.mapDerivedCategoryTwoSquareOfIso` — the two comparisons of
`Stacks.Homology.mapDerivedCategoryCompIso` with the degreewise change of functor in between —
is `CategoryTheory.TwoSquare.mapDerivedCategory`, built from
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` with the derived transformation in
between.

The two ends are identified by `Stacks.Homology.mapDerivedCategoryCompIso_refl_eq` and the middle
by `Stacks.Homology.mapDerivedCategoryIsoOfIso_hom`. -/
theorem mapDerivedCategoryTwoSquareOfIso_eq_mapDerivedCategory (α : T ⋙ R ≅ L ⋙ Bo) :
    mapDerivedCategoryTwoSquareOfIso T L R Bo α =
      (TwoSquare.mk T L R Bo α.hom).mapDerivedCategory := by
  dsimp only [mapDerivedCategoryTwoSquareOfIso, TwoSquare.mapDerivedCategory, TwoSquare.mk,
    TwoSquare.natTrans]
  rw [mapDerivedCategoryCompIso_refl_eq T R, mapDerivedCategoryCompIso_refl_eq L Bo,
    mapDerivedCategoryIsoOfIso_hom, Iso.symm_hom, Iso.symm_inv]

end TwoSquare

end Stacks.Homology

namespace Stacks.Cohomology

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y U V : RingedSpace.{u, u}} (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)

section Degreewise

variable [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)]
  [PreservesFiniteLimits (modulePullback i)] [PreservesFiniteColimits (modulePullback i)]
  [PreservesFiniteLimits (modulePullback j)] [PreservesFiniteColimits (modulePullback j)]
  [PreservesFiniteLimits (modulePullback g)] [PreservesFiniteColimits (modulePullback g)]

/-- **The derived image of the comparison of the two iterated pullbacks around a commutative
square is `CategoryTheory.TwoSquare.mapDerivedCategory` of it.**  The square
`Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare`, which
`Stacks.Cohomology.derivedPullbackSquare_eq_mapDerivedCategory` lands at, is the derived image of
`Stacks.Cohomology.pullbackCompSquare` in the sense that
`CategoryTheory.mateEquiv_mapDerivedCategory` speaks of. -/
theorem mapDerivedCategoryPullbackCompSquare_eq_mapDerivedCategory (w : i ≫ f = g ≫ j) :
    mapDerivedCategoryPullbackCompSquare f i j g w =
      (pullbackCompSquare f i j g w).mapDerivedCategory :=
  Stacks.Homology.mapDerivedCategoryTwoSquareOfIso_eq_mapDerivedCategory (modulePullback j)
    (modulePullback f) (modulePullback g) (modulePullback i) (pullbackCompIso f i j g w)

/-- The conjugate, by the four comparisons `L?^* ≅ D(?^*)`, of the derived comparison of the two
iterated derived pullbacks is the derived image of the underived comparison, componentwise.  This
is `Stacks.Cohomology.derivedPullbackSquare_eq_mapDerivedCategory` with the two comparisons on
the source side moved across, and it is the hypothesis `CategoryTheory.mateEquiv_conj` asks of
the two 2-cells. -/
private theorem conj_derivedPullbackSquare (w : i ≫ f = g ≫ j)
    (a : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (mapDerivedCategoryPullbackCompSquare f i j g w).app a =
      (modulePullback g).mapDerivedCategory.map
          ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).inv.app a) ≫
        (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).inv.app
            ((derivedPullback j).obj a) ≫
          (DerivedBaseChange.derivedPullbackSquare i g f j w).app a ≫
            (derivedPullback i).map
                ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom.app a) ≫
              (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).hom.app
                ((modulePullback f).mapDerivedCategory.obj a) := by
  have hsq := NatTrans.congr_app (derivedPullbackSquare_eq_mapDerivedCategory f i j g w) a
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hsq
  dsimp only [TwoSquare.natTrans] at hsq
  rw [hsq]
  refine (CategoryTheory.conj_chase
    ((modulePullback g).mapDerivedCategory.map
      ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).inv.app a))
    ((modulePullback g).mapDerivedCategory.map
      ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).hom.app a))
    ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).inv.app
      ((derivedPullback j).obj a))
    ((derivedPullback g).map
      ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).hom.app a))
    ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).hom.app
      ((modulePullback j).mapDerivedCategory.obj a))
    ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).inv.app
      ((modulePullback j).mapDerivedCategory.obj a))
    _ ?_ ?_ ?_).symm
  · rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
  · exact (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).inv_hom_id_app _
  · exact (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).inv.naturality
      ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).hom.app a)

variable [PreservesFiniteColimits (modulePushforward f)]
  [PreservesFiniteColimits (modulePushforward g)]

/-- The mate, under the two transported derived adjunctions, of the derived image of the
underived comparison of iterated pullbacks is the derived image of the underived base change
map.  This is three of those pieces composed, in a statement small enough that the rewrites
do not have to re-check a motive mentioning the whiskerings of the main result. -/
private theorem mateEquiv_transported_eq (w : i ≫ f = g ≫ j) :
    mateEquiv (((derivedAdjunction f).ofNatIsoLeft
          (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f)).ofNatIsoRight
        (derivedPushforwardComparisonIso f).symm)
      (((derivedAdjunction g).ofNatIsoLeft
          (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g)).ofNatIsoRight
        (derivedPushforwardComparisonIso g).symm)
      (mapDerivedCategoryPullbackCompSquare f i j g w) =
    (TwoSquare.mk (modulePushforward f) (modulePullback i) (modulePullback j)
      (modulePushforward g) (pushforwardRestrictMap f i j g w)).mapDerivedCategory := by
  rw [mapDerivedCategoryPullbackCompSquare_eq_mapDerivedCategory,
    mateEquiv_derivedAdjunction_eq_mapDerivedCategory (i := g) (h := f) (p := j) (q := i),
    pushforwardRestrictMap_eq_mateEquiv]

/-- **The derived base change of [Stacks, Tag 08HY] is the derived image of the underived base
change.**  For a commutative square of ringed spaces along whose four morphisms pullback of
sheaves of modules is exact and along whose two horizontal morphisms pushforward is right exact,
the 2-square `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare` — the mate, under the
derived adjunctions `Lf^* ⊣ Rf_*` and `Lg^* ⊣ Rg_*` of [Stacks, Tag 079W], of the comparison of
the two iterated derived pullbacks — corresponds, under the identifications `Li^* ≅ D(i^*)` and
`Lj^* ≅ D(j^*)` of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory` and
`D(f_*) ≅ Rf_*`, `D(g_*) ≅ Rg_*` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardComparisonIso`, to
`CategoryTheory.TwoSquare.mapDerivedCategory` of the underived base change map
`Stacks.Cohomology.pushforwardRestrictMap`.

The underived map is a mate by `Stacks.Cohomology.pushforwardRestrictMap_eq_mateEquiv`, the mate
operation commutes with passing to derived categories by
`CategoryTheory.mateEquiv_mapDerivedCategory` in the form
`mateEquiv_derivedAdjunction_eq_mapDerivedCategory` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`,
and the two comparisons of iterated pullbacks agree by
`Stacks.Cohomology.derivedPullbackSquare_eq_mapDerivedCategory`.  What transports the mate from
the derived adjunctions to the degreewise ones is `CategoryTheory.mateEquiv_conj`.

Only the commutativity of the square is used: it need not be Cartesian and no arrow need be an
open immersion. -/
theorem derivedBaseChangeSquare_eq_mapDerivedCategory (w : i ≫ f = g ≫ j) :
    (DerivedBaseChange.derivedBaseChangeSquare i g f j w).natTrans ≫
        Functor.whiskerRight
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).hom
            (derivedPushforward g) ≫
          Functor.whiskerLeft (modulePullback i).mapDerivedCategory
            (derivedPushforwardComparisonIso g).inv =
      Functor.whiskerRight (derivedPushforwardComparisonIso f).inv (derivedPullback j) ≫
          Functor.whiskerLeft (modulePushforward f).mapDerivedCategory
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).hom ≫
        ((TwoSquare.mk (modulePushforward f) (modulePullback i) (modulePullback j)
          (modulePushforward g)
          (pushforwardRestrictMap f i j g w)).mapDerivedCategory).natTrans := by
  rw [DerivedBaseChange.derivedBaseChangeSquare_eq_mateEquiv]
  refine (mateEquiv_conj (derivedAdjunction f) (derivedAdjunction g)
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f)
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g)
    (derivedPushforwardComparisonIso f) (derivedPushforwardComparisonIso g)
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j)
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i)
    (DerivedBaseChange.derivedPullbackSquare i g f j w)
    (mapDerivedCategoryPullbackCompSquare f i j g w)
    (conj_derivedPullbackSquare f i j g w)).trans ?_
  rw [mateEquiv_transported_eq]

/-- **The derived base change map of [Stacks, Tag 08HY] at a complex is the derived image of the
underived base change map**, the component form of
`Stacks.Cohomology.derivedBaseChangeSquare_eq_mapDerivedCategory`. -/
theorem derivedBaseChangeMap_eq_mapDerivedCategory (w : i ≫ f = g ≫ j)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    DerivedBaseChange.derivedBaseChangeMap i g f j w K ≫
        (derivedPushforward g).map
            ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).hom.app K) ≫
          (derivedPushforwardComparisonIso g).inv.app
            ((modulePullback i).mapDerivedCategory.obj K) =
      (derivedPullback j).map ((derivedPushforwardComparisonIso f).inv.app K) ≫
        (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).hom.app
            ((modulePushforward f).mapDerivedCategory.obj K) ≫
          ((TwoSquare.mk (modulePushforward f) (modulePullback i) (modulePullback j)
              (modulePushforward g)
              (pushforwardRestrictMap f i j g w)).mapDerivedCategory).app K := by
  have h := NatTrans.congr_app (derivedBaseChangeSquare_eq_mapDerivedCategory f i j g w) K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  dsimp only [TwoSquare.natTrans] at h
  exact h

end Degreewise

end Stacks.Cohomology

end
