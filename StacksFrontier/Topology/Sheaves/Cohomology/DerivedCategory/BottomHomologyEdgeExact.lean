module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.BottomHomologyEdge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ExactFunctorSingleHomology

/-!
# An exact functor carries the bottom-degree edge morphism to the edge morphism

Let `K` be an object of the derived category of an abelian category with no cohomology below the
degree `c`.  `Stacks.BottomHomologyEdge` studies the edge morphism `H ᶜ(K)[-c] ⟶ K` out of the
bottom cohomology object; this file adds the one statement about it that a diagram chase across
an exact functor needs.

Let `F` be an exact additive functor and `Φ` the induced functor on derived categories.  Then
`Φ K` again has no cohomology below `c`, so it carries an edge morphism of its own; the image
`Φ(H ᶜ(K)[-c])` is read as `H ᶜ(Φ K)[-c]` through
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` and
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, and with that reading **`Φ` of the edge
morphism of `K` is the edge morphism of `Φ K`.**

This is the compatibility that the middle factor of the Gysin edge morphism of
[Stacks, Tag 0G8A] — the comparison `ℋ ᶜ_Z(K)[-c] ⟶ R𝓗_Z(K)` of
`Stacks.DeRham.CohomologicalGysin.localCohomologySingleToDerived`, which is
`Stacks.DeRham.CohomologicalGysin.singleHomologyToOfIsGE` at `R𝓗_Z(K)` — lacked when that edge
morphism had to be carried along the forgetful functor to abelian sheaves.

## Main results

* `isGE_mapDerivedCategory_obj`: an exact functor preserves "no cohomology below `c`".
* `mapDerivedCategory_edge`: **the statement above.**

## Implementation notes

The edge morphism is written out as the three-factor composite rather than named, exactly as in
`Stacks.BottomHomologyEdge`, so that this file needs no geometry import; a consumer identifies the
composite with `Stacks.DeRham.CohomologicalGysin.singleHomologyToOfIsGE` by unfolding that
definition.

By `Stacks.BottomHomologyEdge.eq_of_homologyMap_eq` the identity is checked on `H ᶜ`, where it is
`Stacks.ExactFunctorSingleHomology.homologyMap_mapDerivedCategorySingleFunctor` — that the two
identifications of `H ᶜ(Φ(A[-c]))` with `Φ A` agree — together with
`Stacks.BottomHomologyEdge.homologyMap_eq` and three naturalities: that of
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at the edge morphism, that of
`DerivedCategory.singleFunctorCompHomologyFunctorIso`, and
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` against its own inverse.  The chase is
arranged in `edge_formal`, stated at a variable category and applied with `exact` for the reason
recorded in the implementation notes of `Stacks.ExactFunctorSingleHomology`.

**No declaration here carries a `@[stacks ...]` attribute.**  The edge morphism is a construction
of this library and this is a compatibility of it with an exact functor; nothing of the source is
proved.

## References

* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Lemma 13.14.7 (Tag 06XS)](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory Category Limits

namespace Stacks.BottomHomologyEdge

open DerivedCategory

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact functor preserves "no cohomology below `c`".** -/
instance isGE_mapDerivedCategory_obj (c : ℤ) (K : DerivedCategory C₁) [K.IsGE c] :
    (F.mapDerivedCategory.obj K).IsGE c :=
  (DerivedCategory.isGE_iff _ c).2 fun i hi =>
    F.isZero_homologyFunctor_mapDerivedCategory_obj K i
      ((DerivedCategory.isGE_iff K c).1 inferInstance i hi)

/-- The rearrangement of the diagram chase below, at an abstract category: `h1` replaces the last
factor, `h2` cancels the two comparisons of the single functor against each other and `h3` is the
naturality of the identification of `H ᶜ(A[-c])` with `A`.  Stated abstractly and applied with
`exact` because the objects along the composites are definitionally equal in several spellings
each, which `rw` refuses to identify. -/
private lemma edge_formal {D : Type*} [Category* D] {a b d e g : D}
    (hu : a ⟶ b) (hw : b ⟶ d) (hg : d ⟶ e) (α : e ⟶ g) (s : d ⟶ b) (ε : b ⟶ g) (ρ : a ⟶ g)
    (h1 : hg ≫ α = s ≫ ε) (h2 : hw ≫ s = 𝟙 b) (h3 : hu ≫ ε = ρ) :
    (hu ≫ hw ≫ hg) ≫ α = ρ := by
  rw [Category.assoc, Category.assoc, h1, ← Category.assoc hw s, h2, Category.id_comp, h3]

/-- **An exact functor carries the edge morphism `H ᶜ(K)[-c] ⟶ K` to the edge morphism of the
image complex.**  The image `Φ(H ᶜ(K)[-c])` is read as `H ᶜ(Φ K)[-c]` through
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`; with that reading, `Φ` of the edge
morphism of `K` is the edge morphism of `Φ K`.

By `eq_of_homologyMap_eq` this is checked on `H ᶜ`, where it is the coherence
`Stacks.ExactFunctorSingleHomology.homologyMap_mapDerivedCategorySingleFunctor` of the two
identifications of `H ᶜ(Φ(A[-c]))` with `Φ A`, together with `homologyMap_eq` and three
naturalities. -/
theorem mapDerivedCategory_edge (c : ℤ) (K : DerivedCategory C₁) [K.IsGE c] :
    (singleFunctor C₂ c).map ((F.mapDerivedCategoryHomologyIso c).hom.app K) ≫
        (F.mapDerivedCategorySingleFunctor c).inv.app ((homologyFunctor C₁ c).obj K) ≫
          F.mapDerivedCategory.map
            ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K ≫
              (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K) ≫
                inv ((TStructure.t.truncGEπ c).app K)) =
      (truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app (F.mapDerivedCategory.obj K) ≫
        (TStructure.t.truncGE c).map
            ((TStructure.t.truncLTι (c + 1)).app (F.mapDerivedCategory.obj K)) ≫
          inv ((TStructure.t.truncGEπ c).app (F.mapDerivedCategory.obj K)) := by
  refine eq_of_homologyMap_eq c (F.mapDerivedCategory.obj K) _ ?_
  refine (cancel_mono ((F.mapDerivedCategoryHomologyIso c).hom.app K)).1 ?_
  have h1 : (homologyFunctor C₂ c).map
          (F.mapDerivedCategory.map
            ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K ≫
              (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K) ≫
                inv ((TStructure.t.truncGEπ c).app K))) ≫
        (F.mapDerivedCategoryHomologyIso c).hom.app K =
      (homologyFunctor C₂ c).map
          ((F.mapDerivedCategorySingleFunctor c).hom.app ((homologyFunctor C₁ c).obj K)) ≫
        (singleFunctorCompHomologyFunctorIso C₂ c).hom.app
          (F.obj ((homologyFunctor C₁ c).obj K)) :=
    Eq.trans
      ((F.mapDerivedCategoryHomologyIso c).hom.naturality
        ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K ≫
          (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K) ≫
            inv ((TStructure.t.truncGEπ c).app K)))
      (Eq.trans
        (congrArg
          (fun t => (F.mapDerivedCategoryHomologyIso c).hom.app
            ((singleFunctor C₁ c).obj ((homologyFunctor C₁ c).obj K)) ≫ t)
          (congrArg F.map (homologyMap_eq c K)))
        (Stacks.ExactFunctorSingleHomology.homologyMap_mapDerivedCategorySingleFunctor F c
          ((homologyFunctor C₁ c).obj K)).symm)
  have h2 : (homologyFunctor C₂ c).map
          ((F.mapDerivedCategorySingleFunctor c).inv.app ((homologyFunctor C₁ c).obj K)) ≫
        (homologyFunctor C₂ c).map
          ((F.mapDerivedCategorySingleFunctor c).hom.app ((homologyFunctor C₁ c).obj K)) =
      𝟙 _ :=
    Eq.trans ((homologyFunctor C₂ c).map_comp _ _).symm
      (Eq.trans
        (congrArg (homologyFunctor C₂ c).map
          (Iso.inv_hom_id_app (F.mapDerivedCategorySingleFunctor c)
            ((homologyFunctor C₁ c).obj K)))
        ((homologyFunctor C₂ c).map_id _))
  rw [Functor.map_comp, Functor.map_comp]
  exact edge_formal _ _ _ _ _ _ _ h1 h2
    ((singleFunctorCompHomologyFunctorIso C₂ c).hom.naturality
      ((F.mapDerivedCategoryHomologyIso c).hom.app K))

end Stacks.BottomHomologyEdge

end
