module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPostcomposeIndexing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions

/-!
# The two spellings of pulling an exact functor out of a right derived functor

The library has two independent constructions of the comparison that pulls an exact additive
functor out of a right derived functor, and they are not the same declaration:

* `CategoryTheory.Functor.rightDerivedCompIso F G n`, of type
  `(F ⋙ G).rightDerived n ≅ F.rightDerived n ⋙ G`, built by whiskering
  `CategoryTheory.Functor.mapHomotopyCategoryHomologyIso` into the chosen injective
  resolutions, on homotopy categories; and
* `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n`, for `e : F ⋙ G ≅ H`, a
  `CategoryTheory.NatIso.ofComponents` through
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`, going
  `F.rightDerived n ⋙ G ≅ H.rightDerived n`.

The second has the full toolkit of component, transitivity and degree-zero lemmas; the first is
what the indexing coherence
`Stacks.DerivedIndexing.rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes` and hence the
post-composition coherence for
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` are stated with. The two
were not identified; the implementation notes of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision` and of
`StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompCoherence` both recorded that as an
open gap. This file closes it, first at `e = CategoryTheory.Iso.refl` — the only case in which
the two have the same source and target — and then for an arbitrary `e`, where the two targets
are related by `CategoryTheory.Functor.rightDerivedIsoOfNatIso e n`.

## Main results

* `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_refl`: **the two spellings agree.**
  For additive `F` and exact additive `G`,
  `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G (F ⋙ G) (Iso.refl _) n` is the
  inverse of `CategoryTheory.Functor.rightDerivedCompIso F G n`.
* `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_refl_app`: the componentwise form.
* `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso`: **the two spellings agree for an
  arbitrary comparison `e : F ⋙ G ≅ H`**, which is the form the excision of local cohomology
  needs: `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n` is the inverse of
  `CategoryTheory.Functor.rightDerivedCompIso F G n` followed by
  `CategoryTheory.Functor.rightDerivedIsoOfNatIso e n`. Componentwise,
  `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_app`.
* `Stacks.DerivedIndexing.mapComplexHomologyIso_refl_hom_app`,
  `Stacks.DerivedIndexing.mapComplexHomologyIso_hom_app`: the components of
  `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` at the identity comparison and at an
  arbitrary one — the termwise homology comparison
  `Stacks.DerivedIndexing.mapExactHomologyIso`, inverted, followed by the homology of `e` applied
  termwise.

## Implementation notes

Both sides are three-factor composites on the chosen injective resolution, and the three factors
are mutually inverse pairs, so the identification is three cancellations — `cancel3`.

What makes the computation possible on the `ModuleComparison` side is that
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` at the *chosen* resolution is the
comparison of homology on the homotopy category with homology on complexes and nothing else:
`Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution`. On the `Functor` side the
components are `Stacks.DerivedIndexing.rightDerivedCompIso_hom_app` followed by
`Stacks.DerivedIndexing.mapHomotopyCategoryHomologyIso_hom_app_quotient`. Both of those existed;
only the comparison between the two results did not.

`Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` contributes an identity morphism —
the component of `CategoryTheory.Functor.mapHomologicalComplexCompIso` at
`CategoryTheory.Iso.refl` — which is removed by a `congrArg` into
`CategoryTheory.Functor.map_id`, as elsewhere in this tree: `rw` on it is not type-correct,
the two objects agreeing only through semireducible definitions.

**The general case needs no toolkit for varying `H`.** The `ModuleComparison` toolkit covers
varying `G` (`rightDerivedCompIso_hom_app_natTrans`, `rightDerivedCompIso_congr`) but not varying
`H`, and the case `e ≠ CategoryTheory.Iso.refl` does not need it: once both sides are read on the
chosen injective resolution, the only thing left to know about
`CategoryTheory.Functor.rightDerivedIsoOfNatIso e n` is that its component there is `e` applied
termwise, which is Mathlib's `CategoryTheory.InjectiveResolution.rightDerived_app_eq`. The
general case is then the identity case with one factor spliced in.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedIndexing

universe v v' v'' u u' u''

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] [G.PreservesHomology]

/-- A functor carries a pair of mutually inverse morphisms to a pair of mutually inverse
morphisms. Stated at arbitrary categories. -/
theorem map_comp_id {X Y : Type*} [Category* X] [Category* Y] (H : X ⥤ Y) {a b : X}
    (f : a ⟶ b) (g : b ⟶ a) (h : f ≫ g = CategoryStruct.id a) :
    H.map f ≫ H.map g = CategoryStruct.id (H.obj a) := by
  rw [← H.map_comp, h, H.map_id]

/-- Three mutually inverse pairs cancelling. Stated at an arbitrary category with the objects
implicit and the morphisms explicit. -/
private theorem cancel3 {X : Type*} [Category* X] {x y z u : X}
    (a : x ⟶ y) (b : y ⟶ z) (c : z ⟶ u) (c' : u ⟶ z) (b' : z ⟶ y) (a' : y ⟶ x)
    (hc : c ≫ c' = CategoryStruct.id z) (hb : b ≫ b' = CategoryStruct.id y)
    (ha : a ≫ a' = CategoryStruct.id x) :
    (a ≫ b ≫ c) ≫ c' ≫ b' ≫ a' = CategoryStruct.id x := by
  simp [reassoc_of% hc, reassoc_of% hb, ha]

/-- A right inverse of an isomorphism is its inverse. Stated at an arbitrary category. -/
private theorem eq_inv_of_comp {X : Type*} [Category* X] {x y : X} (e : x ≅ y) (g : y ⟶ x)
    (h : e.hom ≫ g = CategoryStruct.id x) : g = e.inv := by
  rw [← cancel_epi e.hom, h, e.hom_inv_id]

omit [EnoughInjectives C] in
/-- **The components of `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` at the
identity comparison.** The reassociation that the definition composes it with has identity
components, so what is left is the termwise comparison of the homology of `G` applied to a
complex with `G` applied to its homology, inverted. -/
theorem mapComplexHomologyIso_refl_hom_app (n : ℕ)
    (K : HomologicalComplex C (ComplexShape.up ℕ)) :
    (Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso F G (F ⋙ G)
        (Iso.refl (F ⋙ G)) n).hom.app K =
      (mapExactHomologyIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n).inv :=
  have h0 : (Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso F G (F ⋙ G)
        (Iso.refl (F ⋙ G)) n).hom.app K =
      (mapExactHomologyIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n).inv ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
            (ComplexShape.up ℕ)).hom.app K) := rfl
  have h1 : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℕ)).hom.app K = CategoryStruct.id
        ((F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) := rfl
  have h2 : (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℕ)).hom.app K) = CategoryStruct.id _ :=
    (congrArg (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map h1).trans
      ((HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map_id _)
  h0.trans ((congrArg (fun z =>
    (mapExactHomologyIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n).inv ≫ z)
      h2).trans (Category.comp_id _))

/-- The component of `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` on the chosen
injective resolution, with the middle factor replaced by any equal morphism. -/
private theorem moduleComparison_rightDerivedCompIso_hom_app_eq (H : C ⥤ E) [H.Additive]
    (e : F ⋙ G ≅ H) (n : ℕ) (X : C)
    {φ : G.obj (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution X).cocomplex).homology n) ⟶
      ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution X).cocomplex).homology n}
    (h : (Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso F G H e n).hom.app
      (injectiveResolution X).cocomplex = φ) :
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n).hom.app X =
      G.map ((injectiveResolution X).isoRightDerivedObj F n).hom ≫ φ ≫
        ((injectiveResolution X).isoRightDerivedObj H n).inv :=
  h ▸ rfl

/-- **The two spellings agree, componentwise.** -/
theorem moduleComparison_rightDerivedCompIso_refl_app (n : ℕ) (X : C) :
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G (F ⋙ G)
        (Iso.refl (F ⋙ G)) n).hom.app X = (F.rightDerivedCompIso G n).inv.app X := by
  refine eq_inv_of_comp ((F.rightDerivedCompIso G n).app X) _ ?_
  have hA : ((F.rightDerivedCompIso G n).app X).hom =
      (HomotopyCategory.homologyFunctorFactors E (ComplexShape.up ℕ) n).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution X).cocomplex)) ≫
        (mapExactHomologyIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution X).cocomplex) n).hom ≫
          G.map ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution X).cocomplex)) :=
    (rightDerivedCompIso_hom_app F G n X).trans
      (mapHomotopyCategoryHomologyIso_hom_app_quotient G _ n)
  have hB : (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G (F ⋙ G)
        (Iso.refl (F ⋙ G)) n).hom.app X =
      G.map ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution X).cocomplex)) ≫
        (mapExactHomologyIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution X).cocomplex) n).inv ≫
          ((HomotopyCategory.homologyFunctorFactors E (ComplexShape.up ℕ) n).app
            (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution X).cocomplex)).inv := by
    have hIR : (injectiveResolution X).isoRightDerivedObj (F ⋙ G) n =
        (HomotopyCategory.homologyFunctorFactors E (ComplexShape.up ℕ) n).app
          (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution X).cocomplex) :=
      Iso.ext (isoRightDerivedObj_injectiveResolution (F ⋙ G) X n)
    refine (moduleComparison_rightDerivedCompIso_hom_app_eq F G (F ⋙ G) (Iso.refl (F ⋙ G)) n X
      (mapComplexHomologyIso_refl_hom_app F G n _)).trans ?_
    rw [isoRightDerivedObj_injectiveResolution, congrArg Iso.inv hIR]
    rfl
  rw [hA, hB]
  exact cancel3 _ _ _ _ _ _
    (map_comp_id G _ _ (Iso.inv_hom_id_app _ _)) (Iso.hom_inv_id _)
    (Iso.hom_inv_id_app _ _)

/-- **The two spellings of pulling an exact functor out of a right derived functor agree.** For
additive `F : 𝒞 ⥤ 𝒟` with `𝒞` having enough injectives and additive `G : 𝒟 ⥤ ℰ` preserving
homology, `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at the identity comparison is
the inverse of `CategoryTheory.Functor.rightDerivedCompIso`. -/
theorem moduleComparison_rightDerivedCompIso_refl (n : ℕ) :
    Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G (F ⋙ G) (Iso.refl (F ⋙ G)) n =
      (F.rightDerivedCompIso G n).symm :=
  Iso.ext (NatTrans.ext (funext (moduleComparison_rightDerivedCompIso_refl_app F G n)))

/-! ### A general comparison `e : F ⋙ G ≅ H` -/

section General

variable (H : C ⥤ E) [H.Additive] (e : F ⋙ G ≅ H)

omit [EnoughInjectives C] in
/-- **The components of `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` at an
arbitrary comparison `e : F ⋙ G ≅ H`**: the termwise comparison of the homology of `G` applied
to a complex with `G` applied to its homology, inverted, followed by the homology of `e` applied
termwise.

True by definition; recorded because `rw` cannot reach the two spellings
`(F ⋙ G).mapHomologicalComplex c` and `F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c`
of the source of `CategoryTheory.Functor.mapHomologicalComplexCompIso`. -/
theorem mapComplexHomologyIso_hom_app (n : ℕ)
    (K : HomologicalComplex C (ComplexShape.up ℕ)) :
    (Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso F G H e n).hom.app K =
      (mapExactHomologyIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n).inv ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℕ)).app K) := rfl

/-- Splicing a mutually inverse pair into the middle of a four-factor composite. Stated at an
arbitrary category with the objects implicit and the morphisms explicit. -/
theorem splice {X : Type*} [Category* X] {x y z u v w : X}
    (a : x ⟶ y) (b : y ⟶ z) (p : z ⟶ u) (q : u ⟶ z) (c : z ⟶ v) (d : v ⟶ w)
    (hpq : p ≫ q = CategoryStruct.id z) :
    a ≫ (b ≫ c) ≫ d = (a ≫ b ≫ p) ≫ q ≫ c ≫ d := by
  simp [reassoc_of% hpq]

/-- **The two spellings agree for an arbitrary comparison, componentwise.** -/
theorem moduleComparison_rightDerivedCompIso_app (n : ℕ) (X : C) :
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n).hom.app X =
      (F.rightDerivedCompIso G n).inv.app X ≫
        (Functor.rightDerivedIsoOfNatIso e n).hom.app X := by
  have hA : (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n).hom.app X =
      G.map ((injectiveResolution X).isoRightDerivedObj F n).hom ≫
        ((mapExactHomologyIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution X).cocomplex) n).inv ≫
            (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
              ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℕ)).app
                (injectiveResolution X).cocomplex)) ≫
          ((injectiveResolution X).isoRightDerivedObj H n).inv :=
    moduleComparison_rightDerivedCompIso_hom_app_eq F G H e n X
      (mapComplexHomologyIso_hom_app F G H e n _)
  have hB : (F.rightDerivedCompIso G n).inv.app X =
      G.map ((injectiveResolution X).isoRightDerivedObj F n).hom ≫
        (mapExactHomologyIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution X).cocomplex) n).inv ≫
          ((injectiveResolution X).isoRightDerivedObj (F ⋙ G) n).inv :=
    (moduleComparison_rightDerivedCompIso_refl_app F G n X).symm.trans
      (moduleComparison_rightDerivedCompIso_hom_app_eq F G (F ⋙ G) (Iso.refl (F ⋙ G)) n X
        (mapComplexHomologyIso_refl_hom_app F G n _))
  have hC : (Functor.rightDerivedIsoOfNatIso e n).hom.app X =
      ((injectiveResolution X).isoRightDerivedObj (F ⋙ G) n).hom ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
            ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℕ)).app
              (injectiveResolution X).cocomplex) ≫
          ((injectiveResolution X).isoRightDerivedObj H n).inv :=
    InjectiveResolution.rightDerived_app_eq e.hom (injectiveResolution X) n
  rw [hA, hB, hC]
  exact splice _ _ _ _ _ _
    (Iso.inv_hom_id ((injectiveResolution X).isoRightDerivedObj (F ⋙ G) n))

/-- **The two spellings of pulling an exact functor out of a right derived functor agree, for an
arbitrary comparison.** For additive `F : 𝒞 ⥤ 𝒟` with `𝒞` having enough injectives, additive
`G : 𝒟 ⥤ ℰ` preserving homology and `e : F ⋙ G ≅ H`,
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n` is the inverse of
`CategoryTheory.Functor.rightDerivedCompIso F G n` followed by
`CategoryTheory.Functor.rightDerivedIsoOfNatIso e n`.

At `e = CategoryTheory.Iso.refl` the second factor is the identity, which recovers
`moduleComparison_rightDerivedCompIso_refl`; the content beyond that case is that
`CategoryTheory.NatTrans.rightDerived` of `e` is, on the chosen injective resolution, `e` applied
termwise — `CategoryTheory.InjectiveResolution.rightDerived_app_eq`. -/
theorem moduleComparison_rightDerivedCompIso (n : ℕ) :
    Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n =
      (F.rightDerivedCompIso G n).symm ≪≫ Functor.rightDerivedIsoOfNatIso e n :=
  Iso.ext (NatTrans.ext (funext (moduleComparison_rightDerivedCompIso_app F G H e n)))

end General

end Stacks.DerivedIndexing

end
