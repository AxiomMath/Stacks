module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorExtendHomotopyHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# An exact functor and the homology of the derived category, read on the homotopy category

`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` says that an exact additive functor
`F : C₁ ⥤ C₂` commutes with the homology functors of the unbounded derived categories,
`Hⁿ(F.mapDerivedCategory K) ≅ F(Hⁿ K)`. It is built by the universal property of the localization
`DerivedCategory.Q`, so nothing about it is visible at an object of the derived category which is
not of the form `Q.obj M`. This file computes it at `DerivedCategory.Qh.obj K` for an arbitrary
`K` in the homotopy category of cochain complexes, in terms of the three comparisons a consumer
on the homotopy category has: `CategoryTheory.Functor.mapDerivedCategoryFactorsh`,
`DerivedCategory.homologyFunctorFactorsh` and
`CategoryTheory.Functor.mapHomotopyCategoryHomologyIso`.

**Why this statement exists.** It is one of the two derived-category halves of the
*post-composition* coherence for the bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` between a right derived
functor on the unbounded derived category and Mathlib's `CategoryTheory.Functor.rightDerived`:
the bridge is assembled out of `DerivedCategory.homologyFunctorFactorsh` whiskered into
`Stacks.DerivedIndexing.resH ⋙ w.mapHomotopyCategory (ComplexShape.up ℤ)`, so reading the bridge
for `w ⋙ G` at `Rw ⋙ G.mapDerivedCategory` asks exactly how `mapDerivedCategoryHomologyIso`
interacts with `homologyFunctorFactorsh`. The classical, `ℕ`-indexed half of that coherence is
`Stacks.DerivedIndexing.rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes`, whose
implementation notes record the present statement as missing.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_hom_app_Q`: the components of
  `mapDerivedCategoryHomologyIso` at `DerivedCategory.Q.obj M`, which are the components of the
  datum it was lifted from and nothing else.
* `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_hom_app_Qh`: **an exact functor commutes
  with the homology of the derived category compatibly with the factorisations of both through
  the homotopy category.** Stated for an arbitrary object of the homotopy category;
  `..._Qh_quotient` is the same statement with that object spelled as the class of a complex.

## Implementation notes

**At `Q.obj M`.** `mapDerivedCategoryHomologyIso` is a `CategoryTheory.Localization.liftNatIso`,
so its `hom` *is* a `CategoryTheory.Localization.liftNatTrans` — by `rfl`, a projection — and
`CategoryTheory.Localization.liftNatTrans_app` computes it at `Q.obj M`. The two
`CategoryTheory.Localization.Lifting.iso`s that appear there are
`CategoryTheory.Localization.Lifting.compRight` of the instance carrying
`mapDerivedCategoryFactors`, and `CategoryTheory.Localization.Lifting.compLeft`, which is
`CategoryTheory.Iso.refl`; after the identities contributed by the associators of
`mapDerivedCategoryHomologyIsoAux` are cancelled, what is left is `rfl`.

**From `Q` to `Qh`.** `DerivedCategory.Qh` is not `@[expose]`, so `Qh.obj (quotient.obj M)` and
`Q.obj M` are *not* `rfl`; the two are related by `DerivedCategory.quotientCompQhIso`, and the
chase carries it. Each of the three comparisons on the homotopy category has a component at the
class of a complex which inserts a copy of that isomorphism —
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app`,
`DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj` and its `inv` form, together with
`Stacks.DerivedIndexing.mapHomotopyCategoryHomologyIso_hom_app_quotient` — and once all four are
substituted, every inserted copy cancels against the one next to it except the two outermost,
which are absorbed by the naturality of `mapDerivedCategoryHomologyIso` itself along
`quotientCompQhIso`. That is the whole content: four cancellations and one naturality square.

**Every step is a helper at a variable category, applied with `exact`.** The ambient category of
the goal is the variable `C₂`, but the morphisms being folded live in `DerivedCategory C₂` and in
the homotopy categories, where `rw [Category.assoc]` is not type-correct under `implicit`
transparency. `map_fold`, `map_unfold`, `id_mid`, `map_map_id` and `chase` are therefore stated at
arbitrary categories with the objects implicit and the morphisms explicit, so that applying one
never asks the elaborator to solve for an object. The one place an identity morphism between two
spellings of a single object has to be recognised — the component of
`CategoryTheory.Functor.mapHomotopyCategoryFactors`, which is `CategoryTheory.Iso.refl` — is
taken in two term-mode steps, a `congrArg` into `CategoryTheory.Functor.map_id`, because `rw` on
it reports that the motive is not type-correct.

**The general form from the quotient form.** An object of `HomotopyCategory C₁ c` is a structure
with one field, so `K` and `(HomotopyCategory.quotient _ _).obj K.as` are definitionally equal and
`..._Qh` is `..._Qh_quotient` at `K.as`.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The components of `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at the image of a
complex.** At `DerivedCategory.Q.obj M` the comparison is the datum it was lifted from: the
factorisation of `F.mapDerivedCategory` through `Q`, the factorisation of the homology functor of
`D(C₂)` through `Q`, the termwise comparison `mapHomologicalComplexHomologyIso`, and the
factorisation of the homology functor of `D(C₁)` through `Q`, inverted. -/
theorem mapDerivedCategoryHomologyIso_hom_app_Q (n : ℤ) (M : CochainComplex C₁ ℤ) :
    (F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj M) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app M) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
          (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app M ≫
            F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app M) := by
  have h : (F.mapDerivedCategoryHomologyIso n).hom = Localization.liftNatTrans
      DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        DerivedCategory.homologyFunctor C₂ n)
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C₁ n ⋙ F)
      (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n)
      (DerivedCategory.homologyFunctor C₁ n ⋙ F)
      (F.mapDerivedCategoryHomologyIsoAux n).hom := rfl
  rw [h, Localization.liftNatTrans_app]
  simp only [Functor.mapDerivedCategoryHomologyIsoAux, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Localization.Lifting.compRight_iso, Localization.Lifting.compLeft_iso, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
  rfl

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
/-- **The two spellings of the comparison of the homology of `F` applied termwise to a complex
with `F` applied to its homology agree.** `Stacks.DerivedIndexing.mapExactHomologyIso` is the
comparison at one complex and one degree, and
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso` is the same comparison as a natural
isomorphism of functors; both are `CategoryTheory.ShortComplex.mapHomologyIso` at the degree-`n`
short complex, so this holds by definition. It is the crossing the chase below closes over. -/
theorem mapExactHomologyIso_hom_eq (n : ℤ) (M : CochainComplex C₁ ℤ) :
    (Stacks.DerivedIndexing.mapExactHomologyIso F M n).hom =
      (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app M := rfl

/-- Four factors under a functor, with the last two cancelling against a fifth factor outside it.
Stated at arbitrary categories with the objects implicit and the morphisms explicit. -/
private theorem map_fold {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {w x y z v : D} (a : w ⟶ x) (b : x ⟶ y) (c : y ⟶ z) (d : z ⟶ v) (e : v ⟶ y)
    (hcd : c ≫ d ≫ e = CategoryStruct.id y) :
    H.map (a ≫ b ≫ c ≫ d) ≫ H.map e = H.map a ≫ H.map b := by
  rw [← H.map_comp, ← H.map_comp]
  exact congrArg H.map (by simp only [Category.assoc, hcd, Category.comp_id])

/-- A functor applied to a three-factor composite, with its first factor cancelling against a
preceding one. Stated at arbitrary categories with the objects implicit. -/
private theorem map_unfold {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {w x y z : D} (ki : w ⟶ x) (k : x ⟶ w) (l : w ⟶ y) (m : y ⟶ z)
    (hk : ki ≫ k = CategoryStruct.id w) :
    H.map ki ≫ H.map (k ≫ l ≫ m) = H.map l ≫ H.map m := by
  rw [← H.map_comp, ← H.map_comp]
  exact congrArg H.map (by rw [← Category.assoc, hk, Category.id_comp])

/-- A pair of mutually inverse morphisms with an identity between them. Stated at an arbitrary
category; `hd` is a hypothesis rather than a rewrite because the identity in question is between
two spellings of one object. -/
private theorem id_mid {D : Type*} [Category* D] {x y : D} (c : x ⟶ y) (d : y ⟶ y) (e : y ⟶ x)
    (hd : d = CategoryStruct.id y) (hce : c ≫ e = CategoryStruct.id x) :
    c ≫ d ≫ e = CategoryStruct.id x := by
  rw [hd, Category.id_comp, hce]

/-- Two functors carry a pair of mutually inverse morphisms to a pair of mutually inverse
morphisms. Stated at arbitrary categories. -/
private theorem map_map_id {D E E' : Type*} [Category* D] [Category* E] [Category* E']
    (H : D ⥤ E) (K : E ⥤ E') {x y : D} (u : x ⟶ y) (v : y ⟶ x)
    (h : u ≫ v = CategoryStruct.id x) :
    K.map (H.map u) ≫ K.map (H.map v) = CategoryStruct.id (K.obj (H.obj x)) := by
  rw [← K.map_comp, ← H.map_comp, h, H.map_id, K.map_id]

/-- **The chase.** A morphism `L` equals a four-factor composite, given: that the first factor
followed by the first half of the second is a two-factor composite `A₁ ≫ B₁` (`hA`); that the
last factor preceded by the tail of the third is `Fl ≫ Fa` (`hD`); that the two middle inner
factors `gi` and `g` are mutually inverse (`hg`); the value `hQ` of the morphism `I` the
naturality square `hnat` relates `L` to; and that `Fq` and `Fa` are mutually inverse (`hk`).
Stated at an arbitrary category with every object implicit and every morphism explicit, so that
applying it never asks the elaborator to solve an object metavariable. -/
private theorem chase {D : Type*} [Category* D] {s t z u y₁ y₂ y₃ y₄ y₅ y₆ : D}
    (L : s ⟶ t) (A : s ⟶ y₁) (E' : y₁ ⟶ y₂) (f : y₂ ⟶ y₃) (gi : y₃ ⟶ y₄) (g : y₄ ⟶ y₃)
    (h : y₃ ⟶ y₅) (ki : y₅ ⟶ y₆) (DD : y₆ ⟶ t)
    (A₁ : s ⟶ z) (B₁ : z ⟶ y₂) (I : z ⟶ u) (Fl : y₅ ⟶ u) (Fq : t ⟶ u) (Fa : u ⟶ t)
    (hA : A ≫ E' = A₁ ≫ B₁) (hD : ki ≫ DD = Fl ≫ Fa)
    (hg : gi ≫ g = CategoryStruct.id y₃) (hQ : I = B₁ ≫ f ≫ h ≫ Fl)
    (hnat : A₁ ≫ I = L ≫ Fq) (hk : Fq ≫ Fa = CategoryStruct.id t) :
    L = A ≫ (E' ≫ f ≫ gi) ≫ (g ≫ h ≫ ki) ≫ DD := by
  rw [← Category.comp_id L, ← hk, ← Category.assoc, ← hnat, hQ]
  simp only [Category.assoc, reassoc_of% hA, reassoc_of% hg, hD]

/-- **`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` is compatible with the
factorisations through the homotopy category, at the class of a complex.** See
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso_hom_app_Qh` for the statement at an
arbitrary object of the homotopy category, which is this one. -/
theorem mapDerivedCategoryHomologyIso_hom_app_Qh_quotient (n : ℤ) (M : CochainComplex C₁ ℤ) :
    (F.mapDerivedCategoryHomologyIso n).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj M)) =
      (DerivedCategory.homologyFunctor C₂ n).map
          (F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj M)) ≫
        (DerivedCategory.homologyFunctorFactorsh C₂ n).hom.app
            ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
          (F.mapHomotopyCategoryHomologyIso (ComplexShape.up ℤ) n).hom.app
              ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj M) ≫
            F.map ((DerivedCategory.homologyFunctorFactorsh C₁ n).inv.app
              ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj M)) := by
  rw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj,
    DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj,
    F.mapDerivedCategoryFactorsh_hom_app,
    Stacks.DerivedIndexing.mapHomotopyCategoryHomologyIso_hom_app_quotient]
  have h0 : (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app M
      = CategoryStruct.id ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) := rfl
  have h1 : DerivedCategory.Qh.map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app M)
      = CategoryStruct.id (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) :=
    (congrArg DerivedCategory.Qh.map h0).trans (DerivedCategory.Qh.map_id _)
  refine chase _ _ _ _ _ _ _ _ _
    ((DerivedCategory.homologyFunctor C₂ n).map
      (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app M)))
    ((DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app M))
    ((F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj M))
    (F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app M))
    (F.map ((DerivedCategory.homologyFunctor C₁ n).map
      ((DerivedCategory.quotientCompQhIso C₁).hom.app M)))
    (F.map ((DerivedCategory.homologyFunctor C₁ n).map
      ((DerivedCategory.quotientCompQhIso C₁).inv.app M)))
    (map_fold (DerivedCategory.homologyFunctor C₂ n) _ _ _ _ _
      (id_mid _ _ _ h1 (Iso.inv_hom_id_app _ _)))
    (map_unfold F _ _ _ _ (Iso.inv_hom_id_app _ _))
    (Iso.inv_hom_id_app _ _)
    (mapDerivedCategoryHomologyIso_hom_app_Q F n M)
    ((F.mapDerivedCategoryHomologyIso n).hom.naturality
      ((DerivedCategory.quotientCompQhIso C₁).hom.app M))
    (map_map_id (DerivedCategory.homologyFunctor C₁ n) F _ _ (Iso.hom_inv_id_app _ _))

/-- **An exact functor commutes with the homology of the derived category compatibly with the
factorisations of both through the homotopy category.** For an exact additive `F : C₁ ⥤ C₂` and
an object `K` of the homotopy category of cochain complexes in `C₁`, the comparison
`Hⁿ(F.mapDerivedCategory (Qh K)) ≅ F(Hⁿ(Qh K))` is: the factorisation of `F.mapDerivedCategory`
through `Qh`, then the factorisation of the homology functor of `D(C₂)` through `Qh`, then the
comparison `CategoryTheory.Functor.mapHomotopyCategoryHomologyIso` of the homology functors of
the homotopy categories, then the factorisation of the homology functor of `D(C₁)` through `Qh`,
inverted and pushed through `F`.

This is one of the two derived-category statements the *post-composition* coherence for
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` needs; the other is the
computation of the unit of `Rw ⋙ G.mapDerivedCategory` in terms of the unit of `Rw`. -/
theorem mapDerivedCategoryHomologyIso_hom_app_Qh (n : ℤ)
    (K : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Qh.obj K) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactorsh C₂ n).hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          (F.mapHomotopyCategoryHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
            F.map ((DerivedCategory.homologyFunctorFactorsh C₁ n).inv.app K) :=
  mapDerivedCategoryHomologyIso_hom_app_Qh_quotient F n K.as

end CategoryTheory.Functor

end
