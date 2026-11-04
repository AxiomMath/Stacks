module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorExtendHomotopyHomology
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# Postcomposition with an exact functor, and the two indexings of the right derived functors

Let `F : 𝒜 ⥤ ℬ` be additive with `𝒜` having enough injectives and let `G : ℬ ⥤ 𝒞` be additive and
preserve homology. Two comparisons of `R ⁿ(F ⋙ G)` with `R ⁿF` are available:

* `CategoryTheory.Functor.rightDerivedCompIso`, which says `R ⁿ(F ⋙ G) ≅ R ⁿF ⋙ G` — the exact
  functor may be pulled out of the right derived functor; and
* `Stacks.DerivedIndexing.rightDerivedIsoRes`, which identifies each of `R ⁿ(F ⋙ G)` and `R ⁿF`
  with the degree-`n` homology of the functor applied to the chosen injective resolution,
  extended by zero to a complex indexed by `ℤ`.

The two are compatible: that is
`Stacks.DerivedIndexing.rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes`, the main result.
Pulling `G` out of `R ⁿ(F ⋙ G)` and then reading `R ⁿF` on the extended resolution agrees with
reading `R ⁿ(F ⋙ G)` on the extended resolution and pulling `G` out of the homology there, the
latter being `CategoryTheory.Functor.mapHomotopyCategoryHomologyIso`.

**Why this statement exists.** It is the classical, `ℕ`-indexed half of the *post-composition*
coherence for the bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` between a right derived
functor on the unbounded derived category and Mathlib's `CategoryTheory.Functor.rightDerived`:
that the bridge for `w ⋙ G` taken at `Rw ⋙ G.mapDerivedCategory` is the bridge for `w`, read
through `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` and
`CategoryTheory.Functor.rightDerivedCompIso`. The implementation notes of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision` record that coherence as
missing and name this half as what
`Stacks.DerivedIndexing.homologyMap_mapExtendIso_hom_comp` was proved for; this file is the
consumer that was absent.

## Main results

* `Stacks.DerivedIndexing.rightDerivedCompIso_hom_app`: the components of
  `CategoryTheory.Functor.rightDerivedCompIso` are those of
  `CategoryTheory.Functor.mapHomotopyCategoryHomologyIso` at the chosen injective resolution,
  and nothing else.
* `Stacks.DerivedIndexing.rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes`: **pulling an
  exact functor out of a right derived functor is compatible with the comparison of the two
  indexings.**

## Implementation notes

`rightDerivedCompIso` is `CategoryTheory.Functor.mapHomotopyCategoryCompIso` followed by
`CategoryTheory.Functor.mapHomotopyCategoryHomologyIso`, and the first of those, taken at
`CategoryTheory.Iso.refl (F ⋙ G)`, has identity components — but identities of objects whose
types agree only through semireducible definitions, so neither `rw` nor `simp` cancels them.
`rightDerivedCompIso_hom_app` removes them in two term-mode steps, a `congrArg` into
`CategoryTheory.Functor.map_id`, as in
`Stacks.DerivedIndexing.mapHomotopyCategoryHomologyIso_hom_app_quotient`.

The chase is then three rewrites and one naturality square, pasted by the file-scoped
`paste_nat`, which is stated at an arbitrary category with the objects implicit and the morphisms
explicit. Every factor is supplied to it as an argument, so no pattern is matched against the
goal; the two sides are brought into its shape by `congrArg` at an explicit lambda rather than
by `rw`.

Both `Stacks.DerivedIndexing.rightDerivedIsoRes` and the composite
`Stacks.DerivedIndexing.extendMapHomologyIso` it is, at an object, equal to by definition are
used: the decomposition of the comparison for `F ⋙ G` into the one for `G` and the termwise
comparison for `F` is `Stacks.DerivedIndexing.extendMapHomologyIso_hom_comp`, which is stated
for `extendMapHomologyIso`.

## What the coherence needed on top of this, and where it is

Only the `ℕ`-indexed half is here. The post-composition coherence for the bridge needed, on top
of it, two statements about the unbounded derived category that this file says nothing about, and
both are now proved:

* that `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` is compatible with
  `DerivedCategory.homologyFunctorFactorsh` — this is
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_hom_app_Qh` of
  `StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyFactorsh`;
* the computation of the unit of `Rw ⋙ G.mapDerivedCategory` in terms of the unit of `Rw`,
  together with the fact that the composite *is* a right derived functor of `w ⋙ G` — these are
  `Stacks.DerivedFunctor.postcomposeUnit_app` and
  `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose` of
  `StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPostcomposeExact`.

The coherence itself, which consumes this file's main result as its fourth square, is
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app` of
`StacksFrontier.Homology.DerivedIndexing.PostCompositionCoherence`.

A claim recorded here previously was wrong and is corrected rather than deleted, because it sent
work in a direction it did not need to go: the obstruction to the first of those two statements
was recorded as Mathlib lacking component lemmas for `homologyFunctorFactorsh` and for
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` at the class of a complex. Mathlib has both —
`DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj`, its `inv` form, and
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` — and each inserts exactly the copy
of `DerivedCategory.quotientCompQhIso` that `DerivedCategory.Qh` not being `@[expose]` makes
necessary. Carrying that isomorphism is the whole of the difficulty, and it is four
cancellations.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits ComplexShape

namespace Stacks.DerivedIndexing

universe v v' v'' u u' u''

variable {C : Type u} {D : Type u'} {D' : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} D']
  [Abelian C] [Abelian D] [Abelian D'] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] (G : D ⥤ D') [G.Additive] [G.PreservesHomology]

/-- **The components of `CategoryTheory.Functor.rightDerivedCompIso`.** Pulling an exact functor
out of a right derived functor is, at an object, the comparison
`CategoryTheory.Functor.mapHomotopyCategoryHomologyIso` of the homology functors at the chosen
injective resolution: the reassociation of the two functors on homotopy categories that the
definition composes it with has identity components. -/
lemma rightDerivedCompIso_hom_app (n : ℕ) (X : C) :
    (F.rightDerivedCompIso G n).hom.app X =
      (G.mapHomotopyCategoryHomologyIso (ComplexShape.up ℕ) n).hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj ((injectiveResolutions C).obj X)) := by
  have h0 : (F.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℕ)).inv.app
      ((injectiveResolutions C).obj X) = 𝟙 _ := rfl
  have h1 : (HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
        ((F.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℕ)).inv.app
          ((injectiveResolutions C).obj X)) = 𝟙 _ :=
    (congrArg (HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map h0).trans
      ((HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map_id _)
  exact (congrArg (fun w => w ≫
      (G.mapHomotopyCategoryHomologyIso (ComplexShape.up ℕ) n).hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
          ((injectiveResolutions C).obj X))) h1).trans (Category.id_comp _)

/-- One naturality square pasted into a composite split by a functor. Stated at an arbitrary
category with the objects implicit and the morphisms explicit. -/
private lemma paste_nat {E : Type*} [Category* E] {X Y Z Z' W V : E}
    (p : X ⟶ Y) (m : Y ⟶ Z') (gq : Y ⟶ Z) (gr : Z ⟶ Z') (s : Z' ⟶ V) (t : Z ⟶ W) (u : W ⟶ V)
    (hm : m = gq ≫ gr) (hnat : gr ≫ s = t ≫ u) :
    p ≫ m ≫ s = (p ≫ gq ≫ t) ≫ u := by
  rw [hm]
  simp only [Category.assoc]
  rw [hnat]

/-- **Pulling an exact functor out of a right derived functor is compatible with the comparison
of the two indexings of the right derived functors.** For additive `F : 𝒜 ⥤ ℬ` with `𝒜` having
enough injectives and additive `G : ℬ ⥤ 𝒞` preserving homology, the composite
`R ⁿ(F ⋙ G)(X) ≅ G(R ⁿF(X)) ≅ G(H ⁿ(F(I))) ≅ H ⁿ(G(F(I)))`, where `I` is the chosen injective
resolution of `X` extended by zero, is the comparison `rightDerivedIsoRes` for `F ⋙ G`. -/
theorem rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes (n : ℕ) (X : C) :
    (F.rightDerivedCompIso G n).hom.app X ≫
        G.map ((rightDerivedIsoRes F n).hom.app X) ≫
          (G.mapHomotopyCategoryHomologyIso (ComplexShape.up ℤ) (n : ℤ)).inv.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X)) =
      (rightDerivedIsoRes (F ⋙ G) n).hom.app X := by
  have hnat := (G.mapHomotopyCategoryHomologyIso (ComplexShape.up ℤ) (n : ℤ)).inv.naturality
    ((mapExtendHomotopyNatIso F embeddingUpNat).hom.app ((injectiveResolutions C).obj X))
  have hF := extendMapHomologyIso_hom F (injectiveResolution X).cocomplex n
  have hG := (extendMapHomologyIso_hom G
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution X).cocomplex) n).trans
    (mapHomotopyCategoryHomologyIso_comp_extendHomotopy_inv G embeddingUpNat
      (rfl : embeddingUpNat.f n = (n : ℤ))
      ((HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution X).cocomplex))).symm
  have hRHS := extendMapHomologyIso_hom_comp F G (injectiveResolution X).cocomplex n
  refine Eq.trans (congrArg (fun w => w ≫ _) (rightDerivedCompIso_hom_app F G n X)) ?_
  refine Eq.trans ?_ hRHS.symm
  refine Eq.trans ?_ (congrArg (fun w => w ≫ _) hG).symm
  exact paste_nat _ _ _ _ _ _ _ ((congrArg G.map hF).trans (G.map_comp _ _)) hnat

end Stacks.DerivedIndexing

end
