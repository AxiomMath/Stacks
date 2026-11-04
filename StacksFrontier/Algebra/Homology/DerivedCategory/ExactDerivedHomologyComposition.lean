module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomologyComposition

/-!
# The homology comparison on the derived category is compatible with composition

For an exact additive functor `E : 𝒜 ⥤ ℬ` of abelian categories with derived categories,
`Stacks.DerivedFunctor.derivedHomologyIso` is the comparison `H^i(E(K)) ≅ E(H^i(K))` for the
degreewise action of `E` on the unbounded derived category. It is the comparison on complexes
descended along the localization `Q : C(𝒜) ⥤ D(𝒜)`, so it is determined by, and computed on the
image of `Q` by, the comparison on complexes. This file records that computation and deduces
that the comparison is compatible with composition of exact functors: for `F : 𝒜 ⥤ ℬ` and
`G : ℬ ⥤ 𝒞` the comparison for `F ⋙ G` is the comparison for `G`, followed by `G` applied to
the comparison for `F`, the two degreewise actions having first been identified.

## Main results

* `Stacks.DerivedFunctor.derivedHomologyIso_hom_app_Q`: on a complex `K`, the component of the
  comparison at `Q.obj K` is the comparison on complexes at `K`, read through the two
  factorizations of the degreewise action of `E` and of the homology functors through the
  category of complexes.
* `Stacks.DerivedFunctor.mapDerivedCategoryCompIso`: the comparison of the degreewise action of
  a composite of exact functors with the composite of the degreewise actions, together with its
  value on the image of the localization,
  `Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Q`.
* `Stacks.DerivedFunctor.derivedHomologyIso_comp_hom_app_Q` and
  `Stacks.DerivedFunctor.derivedHomologyIso_comp_hom_app`: **the composition law**, on the image
  of the localization and then on every object of the derived category. The comparison for
  `F ⋙ G` is the comparison for `G`, followed by `G` applied to the comparison for `F`, once
  the two degreewise actions have been identified.

## Implementation notes

The composition law is proved first on the image of the localization, with the comparison of the
two degreewise actions written out through
`CategoryTheory.Functor.mapDerivedCategoryFactors` rather than named, and only then upgraded to
every object: a natural transformation out of `D(𝒜)` is determined by its restriction along `Q`,
which is `CategoryTheory.Localization.natTrans_ext`. Both forms are kept, because the written-out
one is what a consumer meeting the degreewise actions through their factorizations rewrites with.

The comparison `mapDerivedCategoryCompIso` needs no datum beyond the two functors: the
degreewise action of `F ⋙ G` on complexes *is* the composite of the two degreewise actions, so
the isomorphism of the restrictions along `Q` which the universal property of the localization
consumes is the identity.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.DerivedFunctor

section Derived

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]

/-- **The comparison `H^i(RE(K)) ≅ E(H^i(K))` on the image of the localization.** It is the
comparison on complexes, conjugated by the factorizations of the derived action of `E` and of
the homology functors through the category of complexes. -/
theorem derivedHomologyIso_hom_app_Q (E : A ⥤ B) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] (i : ℤ)
    (K : CochainComplex A ℤ) :
    (derivedHomologyIso E i).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor B i).map (E.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors B i).hom.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (complexHomologyIso E (ComplexShape.up ℤ) i).hom.app K ≫
        E.map ((DerivedCategory.homologyFunctorFactors A i).inv.app K) := by
  simp [derivedHomologyIso, Localization.liftNatTrans_app]

variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (i : ℤ)

/-- **The derived homology comparison of an exact functor is compatible with composition**, on
the image of the localization. -/
theorem derivedHomologyIso_comp_hom_app_Q (K : CochainComplex A ℤ) :
    (derivedHomologyIso G i).hom.app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        G.map ((derivedHomologyIso F i).hom.app (DerivedCategory.Q.obj K)) =
      (DerivedCategory.homologyFunctor C i).map
          (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
            G.mapDerivedCategoryFactors.hom.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
            (F ⋙ G).mapDerivedCategoryFactors.inv.app K) ≫
        (derivedHomologyIso (F ⋙ G) i).hom.app (DerivedCategory.Q.obj K) := by
  have N1 := (derivedHomologyIso G i).hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  rw [derivedHomologyIso_hom_app_Q F i K, derivedHomologyIso_hom_app_Q (F ⋙ G) i K]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← reassoc_of% N1,
    derivedHomologyIso_hom_app_Q G i ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)]
  simp only [Category.assoc]
  have cancel1 : ∀ {X : C} (f : _ ⟶ X),
      (DerivedCategory.homologyFunctor C i).map
          ((F ⋙ G).mapDerivedCategoryFactors.inv.app K) ≫
        (DerivedCategory.homologyFunctor C i).map
          ((F ⋙ G).mapDerivedCategoryFactors.hom.app K) ≫ f = f := by
    intro X f
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    exact Category.id_comp f
  have cancel2 : ∀ {X : C} (f : _ ⟶ X),
      G.map ((DerivedCategory.homologyFunctorFactors B i).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        G.map ((DerivedCategory.homologyFunctorFactors B i).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫ f = f := by
    intro X f
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    exact Category.id_comp f
  rw [cancel1, cancel2,
    reassoc_of% (complexHomologyIso_comp_hom_app (ComplexShape.up ℤ) i F G K)]
  rfl

/-- **The composite of the degreewise actions of two exact functors on the unbounded derived
category is the degreewise action of the composite.** Both sides lift the degreewise action of
`F ⋙ G` on complexes along the localization `Q : C(𝒜) ⥤ D(𝒜)`, the left hand side because each
factor lifts the degreewise action of that factor. -/
def mapDerivedCategoryCompIso :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors⟩
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ((F ⋙ G).mapDerivedCategory) (Iso.refl _)

/-- The comparison of the degreewise actions on the image of the localization: the two
factorizations through the category of complexes, followed by the inverse of the factorization
for the composite. -/
theorem mapDerivedCategoryCompIso_hom_app_Q (K : CochainComplex A ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (F ⋙ G).mapDerivedCategoryFactors.inv.app K := by
  simp only [mapDerivedCategoryCompIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Iso.refl_hom, NatTrans.id_app, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, NatTrans.comp_app, Category.id_comp, Category.assoc]
  rfl

/-- **The derived homology comparison of an exact functor is compatible with composition.** On
every object of the derived category, the comparison for `F ⋙ G` — read through the comparison
of the degreewise actions — is the comparison for `G`, followed by `G` applied to the comparison
for `F`. -/
theorem derivedHomologyIso_comp_hom_app (L : DerivedCategory A) :
    (derivedHomologyIso G i).hom.app (F.mapDerivedCategory.obj L) ≫
        G.map ((derivedHomologyIso F i).hom.app L) =
      (DerivedCategory.homologyFunctor C i).map
          ((mapDerivedCategoryCompIso F G).hom.app L) ≫
        (derivedHomologyIso (F ⋙ G) i).hom.app L := by
  have key : Functor.whiskerLeft F.mapDerivedCategory (derivedHomologyIso G i).hom ≫
        Functor.whiskerRight (derivedHomologyIso F i).hom G =
      Functor.whiskerRight (mapDerivedCategoryCompIso F G).hom
          (DerivedCategory.homologyFunctor C i) ≫
        (derivedHomologyIso (F ⋙ G) i).hom := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (fun K => ?_)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [mapDerivedCategoryCompIso_hom_app_Q]
    exact derivedHomologyIso_comp_hom_app_Q F G i K
  exact NatTrans.congr_app key L

end Derived

end Stacks.DerivedFunctor

end
