module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TruncGESingleHomology

/-!
# The edge morphism `H ᶜ(K)[-c] ⟶ K` out of the bottom cohomology object

Let `C` be an abelian category with a derived category and let `K` be an object of `D(C)` with no
cohomology below the degree `c`.  The composite

`H ᶜ(K)[-c] ≅ τ^{≥c}τ^{<c+1}K ⟶ τ^{≥c}K ≅ K`

— the inverse of `DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`, then `τ^{≥c}`
applied to the truncation inclusion, then the inverse of the truncation projection, which the
vanishing makes invertible — is the morphism out of which an edge map of a spectral sequence is
built.  It is `Stacks.DeRham.CohomologicalGysin.singleHomologyToOfIsGE`, a bare `def` with no
compatibility lemmas; this file supplies the three statements a consumer needs from it, all of
them consequences of one computation: **the composite induces the canonical identification on
`H ᶜ`**.

This is the mirror image of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TruncGESingleHomology.lean`, which does the
same for the map `K ⟶ H ᵈ(K)[-d]` attached to an object with no cohomology *above* `d`.  The
composite is written out here rather than named, so that this file needs no geometry import; the
consumer identifies it with `singleHomologyToOfIsGE` by unfolding that definition.

## Main results

* `Stacks.BottomHomologyEdge.homologyMap_eq`: **the edge morphism induces the canonical
  identification on `H ᶜ`.**
* `Stacks.BottomHomologyEdge.hom_ext`: two morphisms `A[-c] ⟶ K` into an object with no
  cohomology below `c` which agree on `H ᶜ` are equal.  This is
  `DerivedCategory.bijective_homologyFromSingle_of_isGE`, that is [Stacks, Tag 06XS], in the form
  a diagram chase uses it.
* `Stacks.BottomHomologyEdge.eq_of_homologyMap_eq`: **that property determines the edge
  morphism** — a morphism `H ᶜ(K)[-c] ⟶ K` inducing the canonical identification on `H ᶜ` *is*
  the edge morphism.
* `Stacks.BottomHomologyEdge.naturality`: the edge morphism is natural in `K` among the objects
  with no cohomology below `c`.  The bare `def` is built from `CategoryTheory.inv` of a component
  of `truncGEπ` and so carries no naturality of its own.

## Implementation notes

The computation of `H ᶜ` of the composite is the naturality of the truncation projection
`truncGEπ` at the truncation inclusion `truncLTι`, and nothing else.  What makes it short is that
the three identifications of `H ᶜ` of a truncation with `H ᶜ` which the construction of
`truncGELTIsoHomologyFunctorCompSingleFunctor` goes through were pinned down in
`Stacks.TruncGESingleHomology`: `homologyMap_truncGELTIso_hom_app`,
`truncGECompHomologyFunctorIso_hom_app` and `truncGELTCompHomologyFunctorIso_hom_app`.  Without
those the isomorphism is opaque and no statement about its effect on cohomology is provable.

The hypothesis is spelled `[K.IsGE c]`, from which Mathlib's instance
`CategoryTheory.Triangulated.TStructure.isGE_iff_isIso_truncGEπ_app` provides the invertibility
of `(truncGEπ c).app K` that the composite needs.  `IsIso` is a `Prop`-valued class, so the
inverse written here is the one `singleHomologyToOfIsGE` writes, whatever instance term that
definition supplies.

**No declaration here carries a `@[stacks ...]` attribute.**  `hom_ext` is a restatement of
[Stacks, Tag 06XS], already recorded on
`DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE`; the rest is bookkeeping
about an isomorphism of this library's own making.

## References

* [Stacks Project, Lemma 13.14.7 (Tag 06XS)](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

namespace Stacks.BottomHomologyEdge

open DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The edge morphism `H ᶜ(K)[-c] ⟶ K` induces the canonical identification on `H ᶜ`.**

The composite of the three factors is read on `H ᶜ` one factor at a time: the first is
`Stacks.TruncGESingleHomology.homologyMap_truncGELTIso_hom_app`, and the remaining two are the
naturality of the truncation projection at the truncation inclusion, by which `H ᶜ` of them is
the comparison `τ^{≥c}τ^{<c+1} ⋙ H ᶜ ≅ H ᶜ` that the first factor cancels. -/
theorem homologyMap_eq (c : ℤ) (K : DerivedCategory C) [K.IsGE c] :
    (homologyFunctor C c).map
        ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K ≫
          (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K) ≫
            inv ((TStructure.t.truncGEπ c).app K)) =
      (singleFunctorCompHomologyFunctorIso C c).hom.app ((homologyFunctor C c).obj K) := by
  have hnat := TStructure.t.truncGEπ_naturality c ((TStructure.t.truncLTι (c + 1)).app K)
  simp only [Functor.id_obj] at hnat
  have hA : (homologyFunctor C c).map
          ((TStructure.t.truncGEπ c).app ((TStructure.t.truncLT (c + 1)).obj K)) ≫
        (homologyFunctor C c).map
            ((TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K)) ≫
          (homologyFunctor C c).map (inv ((TStructure.t.truncGEπ c).app K)) =
      (homologyFunctor C c).map ((TStructure.t.truncLTι (c + 1)).app K) := by
    rw [← Functor.map_comp_assoc, hnat, Functor.map_comp, assoc, ← Functor.map_comp,
      IsIso.hom_inv_id, CategoryTheory.Functor.map_id, comp_id]
  have hcore : (homologyFunctor C c).map
          ((TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K)) ≫
        (homologyFunctor C c).map (inv ((TStructure.t.truncGEπ c).app K)) =
      (truncGELTCompHomologyFunctorIso c).hom.app K := by
    rw [Stacks.TruncGESingleHomology.truncGELTCompHomologyFunctorIso_hom_app, ← hA,
      ← Stacks.TruncGESingleHomology.truncGECompHomologyFunctorIso_hom_app c c le_rfl,
      Iso.inv_hom_id_app_assoc]
  rw [Functor.map_comp, Functor.map_comp, hcore,
    ← Stacks.TruncGESingleHomology.homologyMap_truncGELTIso_hom_app, ← assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, id_comp]

/-- **Two morphisms `A[-c] ⟶ K` agreeing on `H ᶜ` are equal**, for `K` with no cohomology below
`c`.  This is `DerivedCategory.bijective_homologyFromSingle_of_isGE`, that is [Stacks, Tag 06XS]:
`A[-c]` corepresents `H ᶜ` on the objects with no cohomology below `c`. -/
theorem hom_ext {c : ℤ} {A : C} {K : DerivedCategory C} [K.IsGE c]
    {f g : (singleFunctor C c).obj A ⟶ K}
    (h : (homologyFunctor C c).map f = (homologyFunctor C c).map g) : f = g :=
  (bijective_homologyFromSingle_of_isGE A K c).injective (by
    simp only [homologyFromSingle_apply, h])

/-- **The edge morphism is the only morphism `H ᶜ(K)[-c] ⟶ K` inducing the canonical
identification on `H ᶜ`.**  This is `homologyMap_eq` and `hom_ext`, and it is the form in which a
diagram chase uses the edge morphism: an identity between two composites ending in it is checked
on `H ᶜ`. -/
theorem eq_of_homologyMap_eq (c : ℤ) (K : DerivedCategory C) [K.IsGE c]
    (φ : (singleFunctor C c).obj ((homologyFunctor C c).obj K) ⟶ K)
    (hφ : (homologyFunctor C c).map φ =
      (singleFunctorCompHomologyFunctorIso C c).hom.app ((homologyFunctor C c).obj K)) :
    φ =
      (truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K ≫
        (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K) ≫
          inv ((TStructure.t.truncGEπ c).app K) :=
  hom_ext (by rw [hφ, homologyMap_eq])

/-- **The edge morphism is natural in `K`** among the objects with no cohomology below `c`: for
`g : K ⟶ K'` with both `K` and `K'` in degrees `≥ c`, the square formed by the two edge morphisms,
by `g` and by `H ᶜ(g)` placed in degree `c` commutes.

The bare composite is built from `CategoryTheory.inv` of a component of `truncGEπ`, so it is a
morphism rather than a component of a natural transformation and has no naturality of its own;
this supplies it, by `hom_ext` and `homologyMap_eq` at `K` and at `K'`. -/
theorem naturality (c : ℤ) {K K' : DerivedCategory C} [K.IsGE c] [K'.IsGE c] (g : K ⟶ K') :
    (singleFunctor C c).map ((homologyFunctor C c).map g) ≫
        ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K' ≫
          (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K') ≫
            inv ((TStructure.t.truncGEπ c).app K')) =
      ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K ≫
          (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K) ≫
            inv ((TStructure.t.truncGEπ c).app K)) ≫ g := by
  have : ((𝟭 (DerivedCategory C)).obj K').IsGE c := inferInstanceAs (K'.IsGE c)
  have hε := (singleFunctorCompHomologyFunctorIso C c).hom.naturality
    ((homologyFunctor C c).map g)
  simp only [Functor.comp_map, Functor.id_map] at hε
  refine hom_ext (((homologyFunctor C c).map_comp _ _).trans
    (Eq.trans ?_ ((homologyFunctor C c).map_comp _ _).symm))
  rw [homologyMap_eq, homologyMap_eq]
  exact hε

end Stacks.BottomHomologyEdge

end
