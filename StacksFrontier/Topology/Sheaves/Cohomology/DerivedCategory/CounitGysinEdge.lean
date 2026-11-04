module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.BottomHomologyEdge

/-!
# The Gysin edge morphism attached to a counit, at a variable abelian category

Let `C` and `D` be abelian categories with derived categories, let

`RH : D(C) ⥤ D(D)`

be a functor — in the intended application the derived functor of sections supported on a closed
subset — let `P : D ⥤ C` be exact, and let

`ε : RH ⋙ P.mapDerivedCategory ⟶ 𝟭 D(C)`

be a transformation, in the intended application the counit of the adjunction
`P ⊣ RH` of [Stacks, Tag 0A3B].  For an object `K` of `D(C)` such that `RH K` has no cohomology
below the degree `c` there is then a canonical morphism

`P(H ᶜ(RH K))[-c] ⟶ K`

of `D(C)`: the edge morphism `H ᶜ(RH K)[-c] ⟶ RH K` of `Stacks.BottomHomologyEdge`, pushed along
`P` and followed by `ε`, the source being read as a single complex through Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

This is the construction of `Stacks.DeRham.CohomologicalGysin.supportedGysinEdge`, which [Stacks,
Tag 0G8A] is built from, with every geometric input replaced by a variable: there `C` is the
category of `𝒪_X`-modules on a ringed space, `D` the category of `𝒪_X|_Z`-modules on a closed
subset, `RH` the derived supported sections and `P` the direct image.  The point of having it
here is that the **same** construction then applies to sheaves of abelian groups, where the
counterpart of the counit is
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportPushCounit`: `supportedGysinEdge` is
defined only for sheaves of modules, and the square of [Stacks, Tag 0G8B] needs an abelian-side
edge morphism to compare it with.

## Main definitions

* `Stacks.CounitGysinEdge.edge`: **the edge morphism `P(H ᶜ(RH K))[-c] ⟶ K`.**

## Main results

* `Stacks.CounitGysinEdge.edge_eq`: the three-factor composite the definition unfolds to, as an
  equation holding by `rfl`.  A consumer identifies a geometric edge morphism with `edge` through
  this rather than by `rw` on the equation lemma of the `def`, which re-typechecks the motive at a
  derived category and exhausts the elaboration budget.
* `Stacks.CounitGysinEdge.edge_naturality`: **the edge morphism is natural in `K`** among the
  objects whose image under `RH` has no cohomology below `c`.

## Implementation notes

The middle factor is written out as the three-factor composite of `Stacks.BottomHomologyEdge`
rather than named, exactly as in that file and in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.BottomHomologyEdgeExact`, so that this
file needs no geometry import.  A consumer identifies the composite with
`Stacks.DeRham.CohomologicalGysin.singleHomologyToOfIsGE` by unfolding that definition, which is
how `edge` is `rfl`-equal to `supportedGysinEdge`.

The hypothesis is an instance binder `[(RH.obj K).IsGE c]` rather than an explicit proof, as in
`Stacks.BottomHomologyEdge`; `CategoryTheory.Triangulated.TStructure.IsGE` is `Prop`-valued, so an
explicit proof supplied by a consumer and the instance found here are definitionally equal and the
identification is unaffected.

The naturality is that of `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, that of the
edge morphism — `Stacks.BottomHomologyEdge.naturality`, the bare composite being built from
`CategoryTheory.inv` of a component of the truncation projection and so carrying no naturality of
its own — and that of `ε`, and nothing else.

**No declaration here carries a `@[stacks ...]` attribute.**  The edge morphism is a construction
of this library; the tagged statement it serves is [Stacks, Tag 0G8A], recorded on
`Stacks.DeRham.CohomologicalGysin.gysinCohomologyMap`.

## References

* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Lemma 20.34.4 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
-/

@[expose] public noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory Category Limits

namespace Stacks.CounitGysinEdge

open DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (RH : DerivedCategory C ⥤ DerivedCategory D) (P : D ⥤ C) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (ε : RH ⋙ P.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C))

/-- **The Gysin edge morphism `P(H ᶜ(RH K))[-c] ⟶ K`** attached to the transformation `ε`: the
edge morphism `H ᶜ(RH K)[-c] ⟶ RH K` out of the bottom cohomology object of `RH K`, pushed along
the exact functor `P` and followed by `ε` at `K`.

The source is read as a single complex on the other side of `P` through
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, which is what makes the first factor
necessary.  This is `Stacks.DeRham.CohomologicalGysin.supportedGysinEdge` with the geometry
replaced by variables. -/
def edge (c : ℤ) (K : DerivedCategory C) [(RH.obj K).IsGE c] :
    (singleFunctor C c).obj (P.obj ((homologyFunctor D c).obj (RH.obj K))) ⟶ K :=
  (P.mapDerivedCategorySingleFunctor c).inv.app ((homologyFunctor D c).obj (RH.obj K)) ≫
    P.mapDerivedCategory.map
        ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app (RH.obj K) ≫
          (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app (RH.obj K)) ≫
            inv ((TStructure.t.truncGEπ c).app (RH.obj K))) ≫
      ε.app K

/-- **The three factors of the edge morphism**, as an equation holding by `rfl`.  This is what a
consumer identifying a geometric edge morphism with `edge` uses: `rw` on the equation lemma of the
`def` re-typechecks the motive at a derived category and does not terminate within the elaboration
budget, while `exact` against this equation does. -/
theorem edge_eq (c : ℤ) (K : DerivedCategory C) [(RH.obj K).IsGE c] :
    edge RH P ε c K =
      (P.mapDerivedCategorySingleFunctor c).inv.app ((homologyFunctor D c).obj (RH.obj K)) ≫
        P.mapDerivedCategory.map
            ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app (RH.obj K) ≫
              (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app (RH.obj K)) ≫
                inv ((TStructure.t.truncGEπ c).app (RH.obj K))) ≫
          ε.app K :=
  rfl

/-- **The edge morphism is natural in `K`** among the objects whose image under `RH` has no
cohomology below `c`: for `g : K ⟶ K'` the square formed by the two edge morphisms, by `g` and by
`P(H ᶜ(RH g))` placed in degree `c` commutes.

Three naturalities and nothing else: that of
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, that of the edge morphism out of the
bottom cohomology object — `Stacks.BottomHomologyEdge.naturality` — and that of `ε`. -/
theorem edge_naturality (c : ℤ) {K K' : DerivedCategory C} [(RH.obj K).IsGE c]
    [(RH.obj K').IsGE c] (g : K ⟶ K') :
    (singleFunctor C c).map (P.map ((homologyFunctor D c).map (RH.map g))) ≫
        edge RH P ε c K' =
      edge RH P ε c K ≫ g := by
  have hsingle := (P.mapDerivedCategorySingleFunctor c).inv.naturality
    ((homologyFunctor D c).map (RH.map g))
  simp only [Functor.comp_map] at hsingle
  have hedge := Stacks.BottomHomologyEdge.naturality c (RH.map g)
  have hε := ε.naturality g
  simp only [Functor.comp_map, Functor.id_map] at hε
  rw [edge_eq, edge_eq, ← Category.assoc, hsingle, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc, hedge, Functor.map_comp, Category.assoc, hε, Category.assoc]

end Stacks.CounitGysinEdge

end
