module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatDerived
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismComposition

/-!
# The cohomology edge morphism of a composite of two left exact functors splits

`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison_comp`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/EdgeMorphismComposition.lean`) says that the complex-level comparison `H^q(F K) ⟶ F(H^q K)` of a
composite `F ⋙ G` of two left exact additive functors is the comparison for `G` at `F K` followed
by `G` of the comparison for `F`. This file carries that identity up to the **edge morphism of an
unbounded right derived functor**, which is the level at which conclusion (c) of
[Stacks, Tag 0EX3] meets it.

The lift is in two steps, and neither touches
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparisonOnHomotopy`: the
localization lift is crossed once and for all by
`Stacks.EdgeCompat.homotopyHomologyComparisonToDerived_app_quotient`
(`EdgeCompatDerived.lean`), which evaluates the transported comparison at a complex in terms of
`…homologyComparison` and the two factorisations of the cohomology functor. Applying that at `F`,
at `G` and at `F ⋙ G` reduces the splitting of the transported comparison to the complex-level
splitting; the derived level then follows from the universal property of
`RFG ⋙ H^q` as a right derived functor.

## Main results

All in the namespace `Stacks.EdgeCompat`.

* `homotopyHomologyComparisonToDerived_comp_app_quotient`: **the transported comparison of a
  composite splits**, at the image of a cochain complex.
* `homotopyHomologyComparisonToDerived_comp_app`: the same at an arbitrary object of the homotopy
  category, every such object being the image of its own underlying complex.
* `derivedHomologyComparison_comp`: **the edge morphism of a composite splits.** For unbounded
  right derived functors `RF`, `RG`, `RFG` of the three degreewise functors and a comparison
  `θ : RFG ⟶ RF ⋙ RG` satisfying the factorisation `hθ` that characterises it, the edge morphism
  `H^q(RFG -) ⟶ (F ⋙ G)(H^q -)` is `H^q(θ)`, then the edge morphism of `G` at `RF -`, then `G` of
  the edge morphism of `F`.

## Implementation notes

*The three middle factors cancel.* The transported comparison for `G` ends with `G` of the two
factorisation isomorphisms of the cohomology functor of `B`, inverted, and the transported
comparison for `F` — read under `G` — begins with the same two, forwards. So the composite of the
two transported comparisons is the complex-level comparison of `G`, then `G` of the complex-level
comparison of `F`, with nothing between them, and `homologyComparison_comp` finishes it. The
cancellation is performed by `map_cancel`, at variables of an abstract category.

*The leading crossing is an identity.* `hθ` carries
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` of `CategoryTheory.Iso.refl (F ⋙ G)`, which at
the image of a complex is the identity on the nose — `CategoryTheory.Functor.mapHomotopyCategory`
of a composite and the composite of the two are the same functor definitionally. It is kept in the
statements, rather than discharged there, because that is the spelling `hθ` and
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app_refl` both use.

*Why the derived level is not proved by a chase.* Both sides are natural transformations out of
`RFG ⋙ H^q`, which is a right derived functor by
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.homologyPostcompose_isRightDerivedFunctor`; so
`CategoryTheory.Functor.rightDerived_ext` reduces the identity to its composite with the unit, and
there `…derivedHomologyComparison_fac_app` replaces each of the three edge morphisms by its
transported comparison. The naturality of the edge morphism of `G` is what moves `RG(αF)` past it.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

namespace Stacks.EdgeCompat

universe vA uA vB uB vC uC

/-- **Two cancelling pairs in the middle of a composite, under a functor.** Stated at variables of
an abstract category, where the cancellation is free; the unifier meets the concrete spelling —
iterated derived functors and their cohomology — only at the application. -/
private theorem map_cancel {Bc Cc : Type*} [Category* Bc] [Category* Cc] (H : Bc ⥤ Cc)
    {X Y W T : Bc} {i₁ : X ⟶ Y} {h₁ : Y ⟶ X} {i₂ : Y ⟶ W} {h₂ : W ⟶ Y}
    (e₂ : i₂ ≫ h₂ = 𝟙 Y) (e₁ : i₁ ≫ h₁ = 𝟙 X) (r : X ⟶ T) :
    H.map i₁ ≫ H.map i₂ ≫ H.map (h₂ ≫ h₁ ≫ r) = H.map r := by
  have h : i₁ ≫ i₂ ≫ h₂ ≫ h₁ ≫ r = r := by
    rw [← Category.assoc i₂, e₂, Category.id_comp, ← Category.assoc, e₁, Category.id_comp]
  rw [← H.map_comp, ← H.map_comp, h]

/-- **The outer reassociation of the splitting chase**, at variables of an abstract category: a
leading identity dropped, a cancelling block in the middle replaced by its value, and the head
factor of the right-hand side expanded. -/
private theorem chase_split {Cc : Type*} [Category* Cc] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ : Cc}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) {i₁ : P₃ ⟶ P₄} {i₂ : P₄ ⟶ P₅}
    {r : P₅ ⟶ P₆} {m : P₃ ⟶ P₆} (hm : i₁ ≫ i₂ ≫ r = m)
    {d : P₂ ⟶ P₆} (hd : d = c ≫ m) :
    𝟙 P₀ ≫ (a ≫ b ≫ c ≫ i₁ ≫ i₂) ≫ r = a ≫ b ≫ d := by
  rw [hd, Category.id_comp, ← hm]
  simp only [Category.assoc]

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]
  (q : ℤ) (Z : CochainComplex A ℤ)

omit [HasDerivedCategory A] [HasDerivedCategory B] [PreservesFiniteLimits F]
  [PreservesFiniteLimits G] in
/-- The crossing `CategoryTheory.Functor.mapHomotopyCategoryCompIso` of
`CategoryTheory.Iso.refl (F ⋙ G)` carries, at the image of a complex, is the identity: the
homotopy-category functor of a composite and the composite of the two homotopy-category functors
agree on that object on the nose. So does its image under `Qh` and under the cohomology functor. -/
private theorem map_qh_mapHomotopyCategoryCompIso_inv_app_quotient :
    (DerivedCategory.homologyFunctor C q).map (DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z))) = 𝟙 _ := by
  change (DerivedCategory.homologyFunctor C q).map (DerivedCategory.Qh.map (𝟙 _)) = 𝟙 _
  simp

/-- **The transported comparison of a composite splits, at a complex.** For `F : A ⥤ B` and
`G : B ⥤ C` additive and left exact and a cochain complex `Z` of objects of `A`, the cohomology of
the crossing of the two spellings of the homotopy-category functor of `F ⋙ G`, followed by the
transported comparison of `G` at `F Z` and by `G` of the transported comparison of `F` at `Z`, is
the transported comparison of `F ⋙ G` at `Z`.

Every occurrence of `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.homotopyHomologyComparisonToDerived` is evaluated by
`homotopyHomologyComparisonToDerived_app_quotient`, after which the two factorisation isomorphisms
of the cohomology functor of `B` cancel in the middle and
`…homologyComparison_comp` is what remains. Nothing is assumed of `Z`. -/
theorem homotopyHomologyComparisonToDerived_comp_app_quotient :
    (DerivedCategory.homologyFunctor C q).map (DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z))) ≫
        (homotopyHomologyComparisonToDerived G q).app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
          G.map ((homotopyHomologyComparisonToDerived F q).app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) =
      (homotopyHomologyComparisonToDerived (F ⋙ G) q).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) := by
  have hd : homologyComparison (F ⋙ G) Z q ≫
        (F ⋙ G).map
          ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).inv.app Z) ≫
        (F ⋙ G).map ((DerivedCategory.homologyFunctorFactorsh A q).inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) =
      homologyComparison G ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) q ≫
        G.map (homologyComparison F Z q ≫
          F.map ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).inv.app Z) ≫
          F.map ((DerivedCategory.homologyFunctorFactorsh A q).inv.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z))) := by
    rw [homologyComparison_comp F G Z q, G.map_comp, G.map_comp, Category.assoc]
    rfl
  rw [homotopyHomologyComparisonToDerived_app_quotient (F ⋙ G) q Z,
    homotopyHomologyComparisonToDerived_app_quotient G q
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z),
    homotopyHomologyComparisonToDerived_app_quotient F q Z,
    map_qh_mapHomotopyCategoryCompIso_inv_app_quotient F G q Z]
  exact chase_split _ _ _
    (map_cancel G
      ((DerivedCategory.homologyFunctorFactorsh B q).inv_hom_id_app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)))
      ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).inv_hom_id_app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))
      _)
    hd

/-- **The transported comparison of a composite splits**, at an arbitrary object of the homotopy
category. This is `homotopyHomologyComparisonToDerived_comp_app_quotient` at the underlying
complex: an object of the homotopy category **is** the image of its own underlying complex, so the
two statements are the same one. -/
theorem homotopyHomologyComparisonToDerived_comp_app
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (DerivedCategory.homologyFunctor C q).map (DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app
            K)) ≫
        (homotopyHomologyComparisonToDerived G q).app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          G.map ((homotopyHomologyComparisonToDerived F q).app K) =
      (homotopyHomologyComparisonToDerived (F ⋙ G) q).app K :=
  homotopyHomologyComparisonToDerived_comp_app_quotient F G q K.as

variable (RF : DerivedCategory A ⥤ DerivedCategory B)
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RG : DerivedCategory B ⥤ DerivedCategory C)
  (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)
  [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
  (RFG : DerivedCategory A ⥤ DerivedCategory C)
  (αFG : (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RFG)
  [RFG.IsRightDerivedFunctor αFG (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (θ : RFG ⟶ RF ⋙ RG)

/-- **The cohomology edge morphism of a composite of two left exact functors splits.** For
`F : A ⥤ B` and `G : B ⥤ C` additive and left exact, unbounded right derived functors `RF`, `RG`
and `RFG` of the three degreewise functors, and a comparison `θ : RFG ⟶ RF ⋙ RG` satisfying the
factorisation `hθ` that characterises it, the edge morphism

> `H^q(RFG -) ⟶ (F ⋙ G)(H^q -)`

of `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison` is the
cohomology of `θ`, followed by the edge morphism of `G` at `RF -`, followed by `G` of the edge
morphism of `F`.

This is the derived-level form of `…homologyComparison_comp`, and the hypotheses are the ones
either edge morphism already needs: K-injective resolutions in `A` and in `B` — which is
[Stacks, Tag 079P] where the categories are sheaves of modules — and `hθ`. Nothing is assumed of
the object.

Both sides are natural transformations out of `RFG ⋙ H^q`, a right derived functor by
`…homologyPostcompose_isRightDerivedFunctor`, so
`CategoryTheory.Functor.rightDerived_ext` reduces the claim to its composite with the unit;
`…derivedHomologyComparison_fac_app` then replaces each of the three edge morphisms by its
transported comparison, the naturality of the edge morphism of `G` moves `RG(αF)` across, and
`homotopyHomologyComparisonToDerived_comp_app` closes it. -/
theorem derivedHomologyComparison_comp
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hB : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hθ : ∀ L : HomotopyCategory A (ComplexShape.up ℤ),
      αFG.app L ≫ θ.app (DerivedCategory.Qh.obj L) =
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
              (ComplexShape.up ℤ)).inv.app L) ≫
          αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          RG.map (αF.app L)) :
    derivedHomologyComparison (F ⋙ G) RFG αFG hA q =
      Functor.whiskerRight θ (DerivedCategory.homologyFunctor C q) ≫
        (Functor.associator RF RG (DerivedCategory.homologyFunctor C q)).hom ≫
          Functor.whiskerLeft RF (derivedHomologyComparison G RG αG hB q) ≫
            (Functor.associator RF (DerivedCategory.homologyFunctor B q) G).inv ≫
              Functor.whiskerRight (derivedHomologyComparison F RF αF hA q) G ≫
                (Functor.associator (DerivedCategory.homologyFunctor A q) F G).hom := by
  have hinst := homologyPostcompose_isRightDerivedFunctor
    ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RFG αFG hA q
  refine Functor.rightDerived_ext (RFG ⋙ DerivedCategory.homologyFunctor C q)
    (Functor.whiskerRight αFG (DerivedCategory.homologyFunctor C q) ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _
    (NatTrans.ext (funext fun L => ?_))
  have hnat : (DerivedCategory.homologyFunctor C q).map (RG.map (αF.app L)) ≫
        (derivedHomologyComparison G RG αG hB q).app (RF.obj (DerivedCategory.Qh.obj L)) =
      (derivedHomologyComparison G RG αG hB q).app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L)) ≫
        G.map ((DerivedCategory.homologyFunctor B q).map (αF.app L)) :=
    (derivedHomologyComparison G RG αG hB q).naturality (αF.app L)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id, Category.id_comp,
    Category.assoc]
  rw [derivedHomologyComparison_fac_app (F ⋙ G) RFG αFG hA q L,
    ← Category.assoc ((DerivedCategory.homologyFunctor C q).map (αFG.app L)),
    ← Functor.map_comp, hθ L, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, reassoc_of% hnat, ← G.map_comp,
    derivedHomologyComparison_fac_app F RF αF hA q L,
    reassoc_of% (derivedHomologyComparison_fac_app G RG αG hB q
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L))]
  exact (homotopyHomologyComparisonToDerived_comp_app F G q L).symm

end Stacks.EdgeCompat

end
