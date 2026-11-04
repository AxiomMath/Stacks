module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompare
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySingleCompIso

/-!
# "An exact functor commutes with `Hⁿ`" against composition and against an isomorphism

An exact additive functor `F` between abelian categories with derived categories commutes with
the degree-`n` cohomology of the derived category, and the project carries four copies of that
comparison: `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`,
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`,
`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso` — these three already
identified with each other — and `Stacks.DerivedFunctor.derivedHomologyIso`.  This file
identifies the fourth with the first three, and uses the identification to carry two structural
laws across:

* the comparison is compatible with **composition** of exact functors, which is
  `Stacks.DerivedFunctor.derivedHomologyIso_comp_hom_app` read through
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`;
* the comparison is compatible with an **isomorphism** of exact functors, read through
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`.

Together the two laws compute the degree-`n` cohomology of any isomorphism of derived functors
assembled out of those two constructions, such as
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso`.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q`: the comparison at the
  image of a cochain complex, in terms of the two canonical factorizations and
  `CategoryTheory.ShortComplex.mapHomologyIso`.
* `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_eq_derivedHomologyIso`: the fourth
  copy of the comparison is the second one.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_eq`: the two copies of "the
  descent of a composite is the composite of the descents" are inverse to each other.
* `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp_app`: **the composition
  law.**  `Hⁿ` of the comparison of the two descents of a composite, followed by the comparison
  for the composite, is the comparison for the outer functor followed by the outer functor
  applied to the comparison for the inner one.
* `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_isoOfNatIso_app`: **the
  isomorphism law.**  `Hⁿ` of the descent of an isomorphism of exact functors intertwines the two
  comparisons with the isomorphism itself, taken at the cohomology.

## Implementation notes

Both laws are proved first as equalities of natural transformations out of
`F.mapDerivedCategory ⋙ Hⁿ` and then evaluated at an object: a natural transformation out of a
derived category is determined by its restriction along `DerivedCategory.Q`
(`CategoryTheory.Localization.natTrans_ext`), and that is the only way in.  On the image of
`DerivedCategory.Q` every comparison involved has a closed form, and what is left is the
corresponding statement on cochain complexes — for composition
`Stacks.DerivedFunctor.complexHomologyIso_comp_hom_app`, and for an isomorphism Mathlib's
`CategoryTheory.ShortComplex.homologyMap_mapNatTrans`.

**No `@[stacks ...]` attribute is attached to any declaration here.**
-/

@[expose] public noncomputable section

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- Natural transformations out of a derived category agree when they agree on the image of
`DerivedCategory.Q`. -/
private lemma natTrans_ext_Q {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category* D] {F G : DerivedCategory C ⥤ D} {α β : F ⟶ G}
    (h : ∀ P : CochainComplex C ℤ,
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) :
    α = β :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) h

namespace CategoryTheory.Functor

/-! ### Formal cancellations -/

/-- Cancelling a natural isomorphism against its inverse at the head of a composite, inside a
functor, at abstract categories. -/
private lemma map_inv_hom_app_cancel {X₀ Y₀ Z₀ : Type*} [Category* X₀] [Category* Y₀]
    [Category* Z₀] {Φ Ψ : X₀ ⥤ Y₀} (α : Φ ≅ Ψ) (W : Y₀ ⥤ Z₀) (x : X₀) {m : Z₀}
    (f : W.obj (Ψ.obj x) ⟶ m) :
    W.map (α.inv.app x) ≫ W.map (α.hom.app x) ≫ f = f := by
  rw [← Category.assoc, ← W.map_comp, Iso.inv_hom_id_app, W.map_id, Category.id_comp]

/-- Cancelling an isomorphism against its inverse at the tail of a three-fold composite, at an
abstract category. -/
private lemma inv_hom_cancel_tail {X₀ : Type*} [Category* X₀] {a b c d : X₀}
    (f : a ⟶ b) (g : b ⟶ c) (α : d ≅ c) :
    (f ≫ g ≫ α.inv) ≫ α.hom = f ≫ g := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Two commuting squares pasted at the tail of a composite, at an abstract category. -/
private lemma square_pair_tail {X₀ : Type*} [Category* X₀] {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : X₀}
    (m : a₀ ⟶ a₁) (u : a₁ ⟶ a₂) (t : a₂ ⟶ a₃) (cg : a₃ ⟶ a₄) (gk : a₄ ⟶ a₅)
    (cf : a₂ ⟶ a₆) (ep : a₆ ⟶ a₄) (fk : a₆ ⟶ a₇) (ee : a₇ ⟶ a₅)
    (h₁ : t ≫ cg = cf ≫ ep) (h₂ : fk ≫ ee = ep ≫ gk) :
    m ≫ (u ≫ t) ≫ cg ≫ gk = m ≫ u ≫ (cf ≫ fk) ≫ ee := by
  simp only [Category.assoc]
  rw [← Category.assoc t cg gk, h₁, Category.assoc cf ep gk, ← h₂]

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

section OneFunctor

variable (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The comparison `Hⁿ(F(K)) ≅ F(Hⁿ(K))` at the image of a cochain complex.**  It is
`CategoryTheory.ShortComplex.mapHomologyIso` on the short complex computing the degree-`n`
homology, read across the factorization of the degreewise action of `F` and the two
factorizations of the cohomology functors through the category of complexes. -/
theorem mapDerivedCategoryHomologyFunctorIso_hom_app_Q (n : ℤ) (P : CochainComplex C₁ ℤ) :
    (F.mapDerivedCategoryHomologyFunctorIso n).hom.app (DerivedCategory.Q.obj P) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app P) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        ((P.sc n).mapHomologyIso F).hom ≫
        F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app P) := by
  have h : (F.mapDerivedCategoryHomologyFunctorIso n).hom.app (DerivedCategory.Q.obj P) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app P) ≫
        ((DerivedCategory.homologyFunctorFactors C₂ n).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (F.mapHomologicalComplexHomologyFunctorIso n).hom.app P) ≫
        F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app P) := by
    simp [mapDerivedCategoryHomologyFunctorIso, lifting_iso_mapDerivedCategory,
      DerivedCategory.liftingHomologyFunctor_iso]
  exact h.trans (whisker_eq _ (Category.assoc _ _ _))

/-- **The fourth copy of "an exact functor commutes with `Hⁿ`" is the second one.**
`Stacks.DerivedFunctor.derivedHomologyIso` and
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` are both
`CategoryTheory.Localization.liftNatIso` of the same comparison on complexes, through the same
two `CategoryTheory.Localization.Lifting` data; they are not `rfl`-equal, and they are equal. -/
theorem mapDerivedCategoryHomologyFunctorIso_eq_derivedHomologyIso (n : ℤ) :
    F.mapDerivedCategoryHomologyFunctorIso n = Stacks.DerivedFunctor.derivedHomologyIso F n := by
  refine Iso.ext (natTrans_ext_Q fun P => ?_)
  rw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
    Stacks.DerivedFunctor.derivedHomologyIso_hom_app_Q,
    Stacks.DerivedFunctor.complexHomologyIso_hom_app]
  rfl

end OneFunctor

end CategoryTheory.Functor

namespace Stacks.DerivedCategoryComparisons

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- **The two copies of "the descent of a composite is the composite of the descents" are
inverse to each other.**  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` is
stated in the direction `(F ⋙ G)ᴰ ≅ Fᴰ ⋙ Gᴰ` and `Stacks.DerivedFunctor.mapDerivedCategoryCompIso`
in the other; on the image of a cochain complex both are the same three-factor composite of
canonical factorizations. -/
theorem mapDerivedCategoryCompIso_inv_eq (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (mapDerivedCategoryCompIso F G).inv =
      (Stacks.DerivedFunctor.mapDerivedCategoryCompIso F G).hom := by
  refine natTrans_ext_Q fun P => ?_
  rw [mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Q]

end Stacks.DerivedCategoryComparisons

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-! ### The composition law -/

/-- **The comparison of an exact functor with `Hⁿ` is compatible with composition**, as an
equality of natural transformations out of `(Fᴰ ⋙ Gᴰ) ⋙ Hⁿ`. -/
theorem mapDerivedCategoryHomologyFunctorIso_comp (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℤ) :
    Functor.whiskerRight
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv
          (DerivedCategory.homologyFunctor C₃ n) ≫
        ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom =
      (show F.mapDerivedCategory ⋙ G.mapDerivedCategory ⋙
            DerivedCategory.homologyFunctor C₃ n ⟶
          DerivedCategory.homologyFunctor C₁ n ⋙ F ⋙ G from
        Functor.whiskerLeft F.mapDerivedCategory
            (G.mapDerivedCategoryHomologyFunctorIso n).hom ≫
          Functor.whiskerRight (F.mapDerivedCategoryHomologyFunctorIso n).hom G) := by
  simp only [mapDerivedCategoryHomologyFunctorIso_eq_derivedHomologyIso,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_eq]
  refine natTrans_ext_Q fun P => ?_
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  exact (Stacks.DerivedFunctor.derivedHomologyIso_comp_hom_app F G n
    (DerivedCategory.Q.obj P)).symm

/-- **The composition law at an object.**  `Hⁿ` of the comparison of the two descents, followed
by the comparison for the composite, is the comparison for the outer functor followed by the
outer functor applied to the comparison for the inner one. -/
theorem mapDerivedCategoryHomologyFunctorIso_comp_app (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℤ)
    (A : DerivedCategory C₁) :
    (DerivedCategory.homologyFunctor C₃ n).map
          ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv.app A) ≫
        ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom.app A =
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (F.mapDerivedCategory.obj A) ≫
        G.map ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app A) :=
  NatTrans.congr_app (mapDerivedCategoryHomologyFunctorIso_comp F G n) A

/-! ### The isomorphism law -/

section NatIso

variable (F G : C₁ ⥤ C₂)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
/-- The isomorphism law on cochain complexes: the degree-`n` homology of the degreewise
isomorphism intertwines the two short-complex comparisons with the isomorphism itself.  This is
Mathlib's `CategoryTheory.ShortComplex.homologyMap_mapNatTrans`. -/
private theorem homologyMap_mapHomologicalComplex_hom_app (n : ℤ) (P : CochainComplex C₁ ℤ) :
    HomologicalComplex.homologyMap
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) n ≫
        ((P.sc n).mapHomologyIso G).hom =
      ((P.sc n).mapHomologyIso F).hom ≫ e.hom.app (P.sc n).homology := by
  have h : HomologicalComplex.homologyMap
      ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) n =
      ((P.sc n).mapHomologyIso F).hom ≫ e.hom.app (P.sc n).homology ≫
        ((P.sc n).mapHomologyIso G).inv :=
    ShortComplex.homologyMap_mapNatTrans (P.sc n) e.hom
  exact (congrArg (fun t => t ≫ ((P.sc n).mapHomologyIso G).hom) h).trans
    (inv_hom_cancel_tail _ _ _)

/-- **The comparison of an exact functor with `Hⁿ` is compatible with an isomorphism of exact
functors**, as an equality of natural transformations out of `Fᴰ ⋙ Hⁿ`. -/
theorem mapDerivedCategoryHomologyFunctorIso_isoOfNatIso (n : ℤ) :
    Functor.whiskerRight
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F G e).hom
          (DerivedCategory.homologyFunctor C₂ n) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom =
      (F.mapDerivedCategoryHomologyFunctorIso n).hom ≫
        Functor.whiskerLeft (DerivedCategory.homologyFunctor C₁ n) e.hom := by
  refine natTrans_ext_Q fun P => ?_
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [isoOfNatIso_hom_app_Q, mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
    mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  have hnat : (DerivedCategory.homologyFunctor C₂ n).map
        (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P)) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        HomologicalComplex.homologyMap
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) n :=
    (DerivedCategory.homologyFunctorFactors C₂ n).hom.naturality
      ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P)
  have he : F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app P) ≫
        e.hom.app ((DerivedCategory.homologyFunctor C₁ n).obj (DerivedCategory.Q.obj P)) =
      e.hom.app (P.sc n).homology ≫
        G.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app P) :=
    e.hom.naturality ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app P)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, map_inv_hom_app_cancel]
  rw [reassoc_of% hnat]
  exact square_pair_tail _ _ _ _ _ _ _ _ _
    (homologyMap_mapHomologicalComplex_hom_app F G e n P) he

/-- **The isomorphism law at an object.**  `Hⁿ` of the descent of an isomorphism of exact
functors, followed by the comparison for the target functor, is the comparison for the source
functor followed by the isomorphism at the degree-`n` cohomology. -/
theorem mapDerivedCategoryHomologyFunctorIso_isoOfNatIso_app (n : ℤ)
    (A : DerivedCategory C₁) :
    (DerivedCategory.homologyFunctor C₂ n).map
          ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F G e).hom.app A) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app A =
      (F.mapDerivedCategoryHomologyFunctorIso n).hom.app A ≫
        e.hom.app ((DerivedCategory.homologyFunctor C₁ n).obj A) :=
  NatTrans.congr_app (mapDerivedCategoryHomologyFunctorIso_isoOfNatIso F G e n) A

end NatIso

end CategoryTheory.Functor

end
