module

public import StacksFrontier.Algebra.Homology.ShortComplex.PreservesLeftHomologyOfComp
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Composition and naturality of the collapse of a right derived functor

`StacksFrontier/CategoryTheory/Abelian/RightDerivedPostcompose.lean` builds the comparisons
`CategoryTheory.Functor.rightDerivedCompIso` and
`CategoryTheory.Functor.rightDerivedCompIsoOfPreservesLeftHomology` of `(F ⋙ E).rightDerived n`
with `F.rightDerived n ⋙ E`. This file proves their composition law, identifies the two where
both are defined, and proves their naturality in the outer and in the inner functor.

## Main results

* `CategoryTheory.Functor.rightDerivedCompIsoOfPreservesLeftHomology_comp` and
  `..._hom_app_comp`: **the composition law for that comparison.**  For a composable pair of
  outer functors the collapse of the composite is the pasting of the two collapses.
* `CategoryTheory.Functor.rightDerivedCompIsoOfPreservesLeftHomology_eq_rightDerivedCompIso`:
  **the two collapses agree wherever both are defined.**  Where `E` preserves all homology the
  pointwise comparison is `rightDerivedCompIso` whiskered on the left by `P`.
* `CategoryTheory.Functor.rightDerivedCompIso_inv_app`: the component of `rightDerivedCompIso`
  written out as a five-fold composite, which is what that identity is read off from.
* `CategoryTheory.Functor.rightDerivedCompIso_inv_naturality` and
  `..._hom_naturality`: **the comparison is natural in the exact functor pulled out.**  A
  natural transformation `E ⟶ E'`, not assumed invertible, crosses the collapse into the right
  derived functor of its whiskering by `F`.
* `CategoryTheory.Functor.mapHomologicalComplexHomologyIso_inv_naturality` and
  `CategoryTheory.Functor.mapHomotopyCategoryHomologyIso_inv_naturality`: the same naturality
  for the two intermediate comparisons.
* `CategoryTheory.Functor.rightDerivedCompIso_inv_naturality_inner` and
  `..._hom_naturality_inner`: **the comparison is natural in the functor being derived** as
  well, so that the collapse can be compared between two different inner functors.

## Implementation notes

`rightDerivedCompIsoOfPreservesLeftHomology` is built component by component out of
`ShortComplex.mapHomologyIso`, so its composition law is an identity between the components, and is
therefore `CategoryTheory.ShortComplex.mapHomologyIso_comp_inv` read on those components; the two
spellings `S.map E ⋙ E'` and `S.map (E ⋙ E')` of one short complex, and
`(F ⋙ E).mapHomologicalComplex c` against `F.mapHomologicalComplex c ⋙ E.mapHomologicalComplex c`,
are definitionally equal, which is why the hypothesis supplied to the second collapse can be handed
to the short-complex law unchanged.

The last step of that proof is `with_unfolding_all`, and it has to be: identifying the component
of the comparison with the short-complex isomorphism means seeing through
`HomotopyCategory.homologyFunctor`, which is `irreducible`, so the definitional unfolding that
the construction above performs with `unfold` is not available to `exact` at default
transparency. The short-complex fact is therefore elaborated first, with instances resolved
normally, and only the final check runs at full transparency.

Comparing the two collapses is the same difficulty one step further out, and `with_unfolding_all`
alone does not settle it: the component of `rightDerivedCompIso` is a five-fold composite four of
whose factors are identities, and `CategoryTheory.Category.id_comp` is propositional, so no amount
of unfolding turns that composite into its middle factor.  It is instead reassociated.
`rightDerivedCompIso_inv_app` writes the composite out — a statement that elaborates at default
transparency, because each junction between consecutive factors is a definitional equality not
involving `HomotopyCategory.homologyFunctor` — and the private `idGlue` cancels the four outer
factors from a shape in which they are morphism variables.  Supplying `idGlue` with the four
`rfl`s, and matching its middle factor against the component of
`rightDerivedCompIsoOfPreservesLeftHomology`, is the one step that runs at full transparency.
Rewriting instead is not available: the five-fold composite is not type-correct at the `implicit`
transparency level that `rw` and `simp only` use for matching, exactly as in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedFunctors/CompositeComparisonTransitivity.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
  {B : Type*} [Category* B] [Abelian B] {B' : Type*} [Category* B'] [Abelian B']

section Composition

variable {B'' : Type*} [Category* B''] [Abelian B''] {D : Type*} [Category* D]

/-- **The composition law for `rightDerivedCompIsoOfPreservesLeftHomology`, at an object.**
Collapsing `E` out of the right derived functor and then `E'`, and collapsing `E ⋙ E'` out in one
step, agree. -/
theorem rightDerivedCompIsoOfPreservesLeftHomology_hom_app_comp (P : D ⥤ A) (F : A ⥤ B)
    [F.Additive] (E : B ⥤ B') [E.Additive] (E' : B' ⥤ B'') [E'.Additive] (n : ℕ)
    (hE : ∀ X : D, E.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (P.obj X)).cocomplex).sc n))
    (hE' : ∀ X : D, E'.PreservesLeftHomologyOf
      ((((F ⋙ E).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (P.obj X)).cocomplex).sc n))
    (hEE' : ∀ X : D, (E ⋙ E').PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (P.obj X)).cocomplex).sc n))
    (X : D) :
    E'.map ((rightDerivedCompIsoOfPreservesLeftHomology P F E n hE).hom.app X) ≫
        (rightDerivedCompIsoOfPreservesLeftHomology P (F ⋙ E) E' n hE').hom.app X =
      (rightDerivedCompIsoOfPreservesLeftHomology P F (E ⋙ E') n hEE').hom.app X := by
  have : E'.PreservesLeftHomologyOf
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (P.obj X)).cocomplex).sc n).map E) := hE' X
  have := hE X
  have := hEE' X
  have key := (ShortComplex.mapHomologyIso_comp_inv
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (P.obj X)).cocomplex).sc n) E E').symm
  with_unfolding_all exact key

/-- **The composition law for `rightDerivedCompIsoOfPreservesLeftHomology`.**  For a composable
pair `E : B ⥤ B'`, `E' : B' ⥤ B''` of outer functors, the collapse of the composite `E ⋙ E'` is
the pasting of the two collapses: the collapse of `E` pushed forward by `E'`, followed by the
collapse of `E'` at the composite inner functor `F ⋙ E`.

Each of the three hypotheses is the pointwise one of
`rightDerivedCompIsoOfPreservesLeftHomology`, asked only of the degree-`n` short complexes of the
chosen injective resolutions; none of the three functors has to be exact.  The third follows from
the first two by `CategoryTheory.Functor.preservesLeftHomologyOf_comp`.

**The asymmetry this law exposes is what makes it usable where the outer functor is not exact.**
The two-step transport
`P ⋙ F.rightDerived n ⋙ E ⋙ E' ≅ P ⋙ (F ⋙ E).rightDerived n ⋙ E'`, namely
`rightDerivedCompIsoOfPreservesLeftHomology P F (E ⋙ E') n hEE' ≪≫
(rightDerivedCompIsoOfPreservesLeftHomology P (F ⋙ E) E' n hE').symm`, consumes `hEE'` and `hE'`
only.  This law says it is `Functor.whiskerRight` of the collapse of `E` alone — but it says so
only when `hE` is available as well, and `hE` is exactly the hypothesis that fails when `E` is
exact only at coefficients the chosen resolution does not meet.  So the transport exists in
situations where the single-step collapse of `E` does not. -/
theorem rightDerivedCompIsoOfPreservesLeftHomology_comp (P : D ⥤ A) (F : A ⥤ B) [F.Additive]
    (E : B ⥤ B') [E.Additive] (E' : B' ⥤ B'') [E'.Additive] (n : ℕ)
    (hE : ∀ X : D, E.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (P.obj X)).cocomplex).sc n))
    (hE' : ∀ X : D, E'.PreservesLeftHomologyOf
      ((((F ⋙ E).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (P.obj X)).cocomplex).sc n))
    (hEE' : ∀ X : D, (E ⋙ E').PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (P.obj X)).cocomplex).sc n)) :
    Functor.whiskerRight (rightDerivedCompIsoOfPreservesLeftHomology P F E n hE).hom E' ≫
        (rightDerivedCompIsoOfPreservesLeftHomology P (F ⋙ E) E' n hE').hom =
      (rightDerivedCompIsoOfPreservesLeftHomology P F (E ⋙ E') n hEE').hom :=
  NatTrans.ext (funext fun X ↦
    rightDerivedCompIsoOfPreservesLeftHomology_hom_app_comp P F E E' n hE hE' hEE' X)

end Composition

section Comparison

variable {D : Type*} [Category* D]

/-- The reassociation behind `rightDerivedCompIsoOfPreservesLeftHomology_eq_rightDerivedCompIso`:
a five-fold composite collapses to its middle factor once the two factors on its left and the two
on its right are identities, the outermost on each side being read under a functor.

Its point is the shape.  In the composite it is applied to, the four outer factors are identities
only after `HomotopyCategory.homologyFunctor` is unfolded, so the hypotheses `u = 𝟙 X₀` and
`b = 𝟙 (G.obj Z)` cannot be *stated* about those factors at default transparency — their two
endpoints are not visibly the same object.  Here they are stated about morphism variables, where
the endpoints are the same by construction, and the application supplies them with `rfl`. -/
private theorem idGlue {O₀ O O' : Type*} [Category* O₀] [Category* O] [Category* O']
    (E : O₀ ⥤ O) (G : O' ⥤ O) {X₀ : O₀} {Z : O'}
    (u : X₀ ⟶ X₀) (m : E.obj X₀ ⟶ G.obj Z) (b : G.obj Z ⟶ G.obj Z) (v w : Z ⟶ Z)
    (hu : u = 𝟙 X₀) (hb : b = 𝟙 (G.obj Z)) (hv : v = 𝟙 Z) (hw : w = 𝟙 Z) :
    (((E.map u ≫ m) ≫ b) ≫ G.map v) ≫ G.map w = m := by
  rw [hu, hb, hv, hw, E.map_id, G.map_id, Category.id_comp, Category.comp_id, Category.comp_id,
    Category.comp_id]

/-- **The component of `rightDerivedCompIso`, written out.**  At `M : A` the inverse of the
comparison `(F ⋙ E).rightDerived n ≅ F.rightDerived n ⋙ E` is the five-fold composite of

* `E` applied to the factorization of the homology functor on the homotopy category of `B`
  through the homology functor on complexes;
* the inverse of `ShortComplex.mapHomologyIso` for `E` at the degree-`n` short complex of `F`
  applied to the chosen injective resolution of `M` — **the only factor carrying content**;
* the same factorization on `B'`, read backwards at the image of that complex;
* the degree-`n` homology of the comparison of `E.mapHomotopyCategory` with
  `E.mapHomologicalComplex` and of the two spellings of `F ⋙ E` on homotopy categories, both of
  which are identities already.

The composite is written with the nesting `Iso.trans` produces, so that this is `rfl`. -/
theorem rightDerivedCompIso_inv_app (F : A ⥤ B) [F.Additive] (E : B ⥤ B') [E.Additive]
    [E.PreservesHomology] (n : ℕ) (M : A) :
    (F.rightDerivedCompIso E n).inv.app M =
      (((E.map ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).hom.app
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
                (injectiveResolution M).cocomplex)) ≫
            ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
                (injectiveResolution M).cocomplex).sc n).mapHomologyIso E).inv) ≫
          (HomotopyCategory.homologyFunctorFactors B' (ComplexShape.up ℕ) n).inv.app
            ((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
                (injectiveResolution M).cocomplex))) ≫
        (HomotopyCategory.homologyFunctor B' (ComplexShape.up ℕ) n).map (𝟙 _)) ≫
      (HomotopyCategory.homologyFunctor B' (ComplexShape.up ℕ) n).map (𝟙 _) := rfl

/-- **The pointwise collapse is the collapse of an exact functor.**  If `E` preserves all
homology then the comparison `rightDerivedCompIsoOfPreservesLeftHomology P F E n hE` built out of
`ShortComplex.mapHomologyIso` is `rightDerivedCompIso` whiskered on the left by `P`, for every
`hE` — `CategoryTheory.Functor.PreservesLeftHomologyOf` is a `Prop`, so the hypothesis cannot
influence the comparison.

This is what lets the composition law
`rightDerivedCompIsoOfPreservesLeftHomology_comp` be applied to a comparison that was built as
`rightDerivedCompIso`, which is the Mathlib-shaped one every construction reaches for when the
outer functor happens to be exact. -/
theorem rightDerivedCompIsoOfPreservesLeftHomology_eq_rightDerivedCompIso (P : D ⥤ A)
    (F : A ⥤ B) [F.Additive] (E : B ⥤ B') [E.Additive] [E.PreservesHomology] (n : ℕ)
    (hE : ∀ X : D, E.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (P.obj X)).cocomplex).sc n)) :
    rightDerivedCompIsoOfPreservesLeftHomology P F E n hE =
      Functor.isoWhiskerLeft P (F.rightDerivedCompIso E n).symm := by
  refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
  change _ = (F.rightDerivedCompIso E n).inv.app (P.obj X)
  rw [rightDerivedCompIso_inv_app]
  with_unfolding_all
    exact (idGlue E (HomotopyCategory.homologyFunctor B' (ComplexShape.up ℕ) n) _ _ _ _ _
      rfl rfl rfl rfl).symm

end Comparison

section Naturality

/-- The reassociation behind `CategoryTheory.Functor.rightDerivedCompIso_inv_naturality`:  a
naturality square whose two sides each carry one trailing factor becomes the square without
them once those factors are identities, the trailing factors being read under a functor.

It has the same point as `idGlue`:  the two factors are identities only after
`HomotopyCategory.homologyFunctor` is unfolded, so `v = 𝟙 Z` cannot be *stated* about them at
default transparency.  Here they are morphism variables, whose endpoints agree by construction,
and the application supplies the two equations with `rfl`. -/
private theorem naturalityGlue {O O' : Type*} [Category* O] [Category* O'] (G : O' ⥤ O)
    {X Y : O} {Z Z' : O'} (a : X ⟶ Y) (m' : Y ⟶ G.obj Z') (v' : Z' ⟶ Z')
    (m : X ⟶ G.obj Z) (v : Z ⟶ Z) (R : G.obj Z ⟶ G.obj Z')
    (hv : v = 𝟙 Z) (hv' : v' = 𝟙 Z') (h : a ≫ m' = m ≫ R) :
    a ≫ m' ≫ G.map v' = (m ≫ G.map v) ≫ R := by
  rw [hv, hv', G.map_id, G.map_id, Category.comp_id, Category.comp_id, h]

/-- **`ShortComplex.mapHomologyIso` is natural in the functor.**  For a natural transformation
`α : E ⟶ E'` of homology-preserving functors, the comparison of the homology of the image with
the image of the homology carries `α` on the homology to the homology of `α` on the short
complex.

This is `CategoryTheory.ShortComplex.homologyMap_mapNatTrans`, which computes the second of
those two in terms of the first and the two comparisons. -/
private theorem mapHomologyIso_inv_naturality_natTrans {E E' : B ⥤ B'} [E.Additive] [E'.Additive]
    [E.PreservesHomology] [E'.PreservesHomology] (α : E ⟶ E')
    (S : ShortComplex B) [S.HasHomology] :
    α.app S.homology ≫ (S.mapHomologyIso E').inv =
      (S.mapHomologyIso E).inv ≫ ShortComplex.homologyMap (S.mapNatTrans α) := by
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp

/-- **`mapHomologicalComplexHomologyIso` is natural in the functor.**  A natural transformation
`α : E ⟶ E'` of homology-preserving functors commutes with the comparison of `E` with the
homology functors on homological complexes, the transformation induced on the images of a
complex being `CategoryTheory.NatTrans.mapHomologicalComplex`.

Both comparisons are `ShortComplex.mapHomologyIso` at the degree-`n` short complex of the
complex, so this is `mapHomologyIso_inv_naturality_natTrans` there. -/
@[reassoc]
theorem mapHomologicalComplexHomologyIso_inv_naturality {E E' : B ⥤ B'} [E.Additive] [E'.Additive]
    [E.PreservesHomology] [E'.PreservesHomology] (α : E ⟶ E') {ι : Type*}
    (c : ComplexShape ι) (n : ι) (K : HomologicalComplex B c) :
    α.app ((HomologicalComplex.homologyFunctor B c n).obj K) ≫
        (E'.mapHomologicalComplexHomologyIso c n).inv.app K =
      (E.mapHomologicalComplexHomologyIso c n).inv.app K ≫
        (HomologicalComplex.homologyFunctor B' c n).map
          ((NatTrans.mapHomologicalComplex α c).app K) :=
  mapHomologyIso_inv_naturality_natTrans α (K.sc n)

/-- **The component of `mapHomotopyCategoryHomologyIso` at the image of a complex, written
out.**  The comparison is lifted through the quotient functor, so at an object of the homotopy
category which is presented by a complex its inverse is the four-fold composite of the
isomorphism it was lifted from:  `E` applied to the factorization of the homology functor on the
homotopy category of `B`, the comparison on complexes, that factorization on `B'` read
backwards, and the homology of the comparison of `E.mapHomotopyCategory` with
`E.mapHomologicalComplex`.

The composite is written with the nesting `Iso.trans` produces, so that this is `rfl`, and the
object is spelled through `HomotopyCategory.quotient` rather than as a structure instance so
that the statement elaborates at default transparency. -/
private theorem mapHomotopyCategoryHomologyIso_inv_app (E : B ⥤ B') [E.Additive]
    [E.PreservesHomology] {ι : Type*} (c : ComplexShape ι) (n : ι)
    (K : HomologicalComplex B c) :
    (E.mapHomotopyCategoryHomologyIso c n).inv.app
        ((HomotopyCategory.quotient B c).obj K) =
      ((E.map ((HomotopyCategory.homologyFunctorFactors B c n).hom.app K) ≫
            (E.mapHomologicalComplexHomologyIso c n).inv.app K) ≫
          (HomotopyCategory.homologyFunctorFactors B' c n).inv.app
            ((E.mapHomologicalComplex c).obj K)) ≫
        (HomotopyCategory.homologyFunctor B' c n).map
          ((E.mapHomotopyCategoryFactors c).inv.app K) := rfl

/-- `CategoryTheory.Functor.mapHomotopyCategoryFactors` is the identity on the image of a
complex:  it is the canonical isomorphism exhibiting a lift through the quotient, whose
components are identities. -/
private theorem mapHomotopyCategoryFactors_inv_app (E : B ⥤ B') [E.Additive]
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex B c) :
    (E.mapHomotopyCategoryFactors c).inv.app K =
      𝟙 ((HomotopyCategory.quotient B' c).obj ((E.mapHomologicalComplex c).obj K)) := rfl

/-- `CategoryTheory.NatTrans.mapHomotopyCategory` at the image of a complex is the quotient of
`CategoryTheory.NatTrans.mapHomologicalComplex` at that complex, which is how it is defined. -/
private theorem mapHomotopyCategory_natTrans_app {E E' : B ⥤ B'} [E.Additive] [E'.Additive]
    (α : E ⟶ E') {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex B c) :
    (NatTrans.mapHomotopyCategory α c).app ((HomotopyCategory.quotient B c).obj K) =
      (HomotopyCategory.quotient B' c).map ((NatTrans.mapHomologicalComplex α c).app K) := rfl

/-- The last square of `mapHomotopyCategoryHomologyIso_inv_naturality`:  past the comparison on
complexes the two sides differ only by the two identity components of
`CategoryTheory.Functor.mapHomotopyCategoryFactors` and by the two spellings of the induced
transformation, so the square commutes.

The cancellation is performed under one application of the homology functor, after the two
factors on each side have been combined by `CategoryTheory.Functor.map_comp`:  the identities
produced by `mapHomotopyCategoryFactors_inv_app` are not matched by `rw` or `simp only` in the
ambient composite, whose morphisms are those of the quotient category. -/
private theorem mapHomotopyCategoryFactors_glue {E E' : B ⥤ B'} [E.Additive] [E'.Additive]
    (α : E ⟶ E') {ι : Type*} (c : ComplexShape ι) (n : ι) (K : HomologicalComplex B c) :
    (HomotopyCategory.homologyFunctor B' c n).map
          ((HomotopyCategory.quotient B' c).map ((NatTrans.mapHomologicalComplex α c).app K)) ≫
        (HomotopyCategory.homologyFunctor B' c n).map
          ((E'.mapHomotopyCategoryFactors c).inv.app K) =
      (HomotopyCategory.homologyFunctor B' c n).map
          ((E.mapHomotopyCategoryFactors c).inv.app K) ≫
        (HomotopyCategory.homologyFunctor B' c n).map
          ((NatTrans.mapHomotopyCategory α c).app ((HomotopyCategory.quotient B c).obj K)) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    mapHomotopyCategoryFactors_inv_app, mapHomotopyCategoryFactors_inv_app,
    mapHomotopyCategory_natTrans_app]
  congr 1
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **`mapHomotopyCategoryHomologyIso` is natural in the functor**, at an object of the homotopy
category presented by a complex.

The comparison is the four-fold composite of `mapHomotopyCategoryHomologyIso_inv_app`, and the
square splits into the naturality of `α` along the factorization of the homology functor,
`mapHomologicalComplexHomologyIso_inv_naturality`, the naturality of that factorization on `B'`,
and `mapHomotopyCategoryFactors_glue`. -/
theorem mapHomotopyCategoryHomologyIso_inv_naturality {E E' : B ⥤ B'} [E.Additive] [E'.Additive]
    [E.PreservesHomology] [E'.PreservesHomology] (α : E ⟶ E') {ι : Type*}
    (c : ComplexShape ι) (n : ι) (K : HomologicalComplex B c) :
    α.app ((HomotopyCategory.homologyFunctor B c n).obj
          ((HomotopyCategory.quotient B c).obj K)) ≫
        (E'.mapHomotopyCategoryHomologyIso c n).inv.app ((HomotopyCategory.quotient B c).obj K) =
      (E.mapHomotopyCategoryHomologyIso c n).inv.app ((HomotopyCategory.quotient B c).obj K) ≫
        (HomotopyCategory.homologyFunctor B' c n).map
          ((NatTrans.mapHomotopyCategory α c).app ((HomotopyCategory.quotient B c).obj K)) := by
  rw [mapHomotopyCategoryHomologyIso_inv_app, mapHomotopyCategoryHomologyIso_inv_app]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc, mapHomologicalComplexHomologyIso_inv_naturality_assoc,
    NatTrans.naturality_assoc]
  simp only [CategoryTheory.Functor.comp_map]
  rw [mapHomotopyCategoryFactors_glue]

/-- **`rightDerivedCompIso` is natural in the exact functor pulled out**, read on the inverse of
the comparison.  For a natural transformation `α : E ⟶ E'` of additive homology-preserving
functors, the square

`α` on `R ⁿF(M)`, then the comparison for `E'`, equals the comparison for `E`, then the right
derived functor of `α` whiskered by `F`,

commutes in every degree and at every object.  This is the statement a consumer needs in order
to move a *non-invertible* natural transformation of the outer functor across the collapse —
the restriction map of a presheaf, say — which neither
`CategoryTheory.Functor.rightDerivedIsoOfNatIso` nor the composition law of
`rightDerivedCompIsoOfPreservesLeftHomology` provides.

The component of the comparison is reassociated by `naturalityGlue` onto the homotopy-category
comparison, where the square is `mapHomotopyCategoryHomologyIso_inv_naturality` at the image of
the chosen injective resolution. -/
theorem rightDerivedCompIso_inv_naturality (F : A ⥤ B) [F.Additive] {E E' : B ⥤ B'}
    [E.Additive] [E'.Additive] [E.PreservesHomology] [E'.PreservesHomology] (α : E ⟶ E')
    (n : ℕ) (M : A) :
    α.app ((F.rightDerived n).obj M) ≫ (F.rightDerivedCompIso E' n).inv.app M =
      (F.rightDerivedCompIso E n).inv.app M ≫
        (NatTrans.rightDerived (Functor.whiskerLeft F α) n).app M := by
  unfold rightDerivedCompIso
  dsimp [NatTrans.rightDerived, NatTrans.rightDerivedToHomotopyCategory]
  refine naturalityGlue (HomotopyCategory.homologyFunctor B' (ComplexShape.up ℕ) n)
    _ _ _ _ _ _ rfl rfl ?_
  exact mapHomotopyCategoryHomologyIso_inv_naturality α (ComplexShape.up ℕ) n
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((injectiveResolutions A).obj M).as)

/-- **`rightDerivedCompIso` is natural in the exact functor pulled out**, read on the comparison
itself.  This is `rightDerivedCompIso_inv_naturality` conjugated by the comparison, which is an
isomorphism. -/
theorem rightDerivedCompIso_hom_naturality (F : A ⥤ B) [F.Additive] {E E' : B ⥤ B'}
    [E.Additive] [E'.Additive] [E.PreservesHomology] [E'.PreservesHomology] (α : E ⟶ E')
    (n : ℕ) (M : A) :
    (F.rightDerivedCompIso E n).hom.app M ≫ α.app ((F.rightDerived n).obj M) =
      (NatTrans.rightDerived (Functor.whiskerLeft F α) n).app M ≫
        (F.rightDerivedCompIso E' n).hom.app M := by
  simpa using (F.rightDerivedCompIso E n).hom.app M ≫=
    rightDerivedCompIso_inv_naturality F α n M =≫ (F.rightDerivedCompIso E' n).hom.app M

/-- **`rightDerivedCompIso` is natural in the functor being derived**, read on the inverse of the
comparison.  For a natural transformation `β : F ⟶ F'` of additive functors and an exact `E`, the
square

`E` of the right derived functor of `β`, then the comparison for `F'`, equals the comparison for
`F`, then the right derived functor of `β` whiskered by `E`,

commutes in every degree and at every object.  Together with
`rightDerivedCompIso_inv_naturality` this is the variance of the collapse in both of its
functors, which is what identifies the comparison of [Stacks, Tag 072W] between two different
objects of the site:  there the functor being derived is sections over the image of the object,
so it moves with the object, while the functor pulled out is restriction of scalars.

The component of the comparison is reassociated by `naturalityGlue` exactly as in
`rightDerivedCompIso_inv_naturality`;  what is left is then no more than the naturality of
`mapHomotopyCategoryHomologyIso` — the object at which it is taken is the one that moves — at
the morphism `CategoryTheory.NatTrans.mapHomotopyCategory β` of the chosen injective
resolution. -/
theorem rightDerivedCompIso_inv_naturality_inner {F F' : A ⥤ B} [F.Additive] [F'.Additive]
    (β : F ⟶ F') (E : B ⥤ B') [E.Additive] [E.PreservesHomology] (n : ℕ) (M : A) :
    E.map ((NatTrans.rightDerived β n).app M) ≫ (F'.rightDerivedCompIso E n).inv.app M =
      (F.rightDerivedCompIso E n).inv.app M ≫
        (NatTrans.rightDerived (Functor.whiskerRight β E) n).app M := by
  unfold rightDerivedCompIso
  dsimp [NatTrans.rightDerived, NatTrans.rightDerivedToHomotopyCategory]
  refine naturalityGlue (HomotopyCategory.homologyFunctor B' (ComplexShape.up ℕ) n)
    _ _ _ _ _ _ rfl rfl ?_
  exact (E.mapHomotopyCategoryHomologyIso (ComplexShape.up ℕ) n).inv.naturality
    ((NatTrans.mapHomotopyCategory β (ComplexShape.up ℕ)).app ((injectiveResolutions A).obj M))

/-- **`rightDerivedCompIso` is natural in the functor being derived**, read on the comparison
itself.  This is `rightDerivedCompIso_inv_naturality_inner` conjugated by the comparison, which
is an isomorphism. -/
theorem rightDerivedCompIso_hom_naturality_inner {F F' : A ⥤ B} [F.Additive] [F'.Additive]
    (β : F ⟶ F') (E : B ⥤ B') [E.Additive] [E.PreservesHomology] (n : ℕ) (M : A) :
    (F.rightDerivedCompIso E n).hom.app M ≫ E.map ((NatTrans.rightDerived β n).app M) =
      (NatTrans.rightDerived (Functor.whiskerRight β E) n).app M ≫
        (F'.rightDerivedCompIso E n).hom.app M := by
  simpa using (F.rightDerivedCompIso E n).hom.app M ≫=
    rightDerivedCompIso_inv_naturality_inner β E n M =≫ (F'.rightDerivedCompIso E n).hom.app M

end Naturality

end CategoryTheory.Functor

end
