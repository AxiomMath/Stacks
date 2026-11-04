module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Equivalence
import StacksCore.Tactic.StacksAttribute

/-!
# The point-resolution hypothesis of Tag 08Q9 along the diagonal

Let `C` be a small category carrying the chaotic topology and let `U_•` be a cosimplicial object
of `C` which is a point resolution in the sense of Tag 08Q9, that is, for which every simplicial
set `Mor_C(U_•, W)` is homotopy equivalent to the constant simplicial set on a singleton. Let
`u : C ⥤ C × C` be the diagonal functor. Then `u(U_•)` is a point resolution of `C × C`:

```
Mor_{C × C}(u(U_•), (W₁, W₂)) = Mor_C(U_•, W₁) × Mor_C(U_•, W₂)
```

degreewise, and a product of finitely many homotopy equivalences of simplicial objects is a
homotopy equivalence, which is Tag 08Q4.

This is the step in the proof of Tag 08QC that precedes the application of Tag 08QA to the
diagonal, giving the identification `Lπ_!(g^{-1}K) = L(π × π)_!(K)` there.

## Main definitions

* `Stacks.ChaoticSite.yonedaPairFam`: the `Bool`-indexed family of simplicial sets
  `Mor_C(U_•, W₁)`, `Mor_C(U_•, W₂)`.
* `Stacks.ChaoticSite.diagYonedaProj`: the two projections out of
  `Mor_{C × C}(u(U_•), (W₁, W₂))`, as a `Bool`-indexed family of maps of simplicial sets.
* `Stacks.ChaoticSite.diagYonedaToPoint`: the unique map
  `Mor_{C × C}(u(U_•), (W₁, W₂)) ⟶ ∗` to the constant simplicial set on a singleton.

## Main results

* `Stacks.ChaoticSite.isLimitDiagYonedaFan`: in each degree the projections exhibit
  `Mor_{C × C}(u(U_•), (W₁, W₂))` as the product of `Mor_C(U_•, W₁)` and `Mor_C(U_•, W₂)`.
* `Stacks.ChaoticSite.isPointResolution_comp_diag`: the image of a point resolution under the
  diagonal functor is a point resolution of `C × C`.
* `Stacks.ChaoticSite.leftDerivedColimitNatIsoDiag`: consequently Tag 08Q9 applies on `C × C` to
  the diagonal image, computing `L_n π_!` there as the homology of the Moore complex of
  `ℱ(u(U_•))`.

## Implementation notes

The product is indexed by `Bool` rather than by `Fin 2` because the two factors are different
simplicial sets, so the family is dependent and a two-constructor index type makes the
definitions reduce by `cases`. Tag 08Q4 is used in the form
`CategoryTheory.SimplicialObject.nonempty_homotopy_and_homotopyEquivalences_of_isLimit`, whose
products are pinned degreewise by limit fans; the fans on the source are
`Stacks.ChaoticSite.isLimitDiagYonedaFan` and the fans on the target are trivial, the constant
simplicial set on a singleton being terminal and hence its own `Bool`-indexed product.

The two maps required by that lemma are taken to be the same map `diagYonedaToPoint`, so only
its third conjunct — that a finite product of homotopy equivalences is a homotopy equivalence —
is used.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08Q4](https://stacks.math.columbia.edu/tag/08Q4)
* [Stacks Project, Tag 08QC](https://stacks.math.columbia.edu/tag/08QC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.ChaoticSite

universe u

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C) (W₁ W₂ : C)

/-- The `Bool`-indexed family of simplicial sets whose factors are `Mor_C(U_•, W₁)` and
`Mor_C(U_•, W₂)`. -/
def yonedaPairFam : Bool → SimplicialObject (Type u)
  | false => U.op ⋙ yoneda.obj W₁
  | true => U.op ⋙ yoneda.obj W₂

/-- `Mor_{C × C}(u(U_•), (W₁, W₂))`, the simplicial set of morphisms from the diagonal image of
a cosimplicial object of `C` to an object of `C × C`. -/
abbrev diagYoneda : SimplicialObject (Type u) :=
  (U ⋙ Functor.diag C).op ⋙ yoneda.obj (W₁, W₂)

/-- The two projections of `Mor_{C × C}(u(U_•), (W₁, W₂))` onto `Mor_C(U_•, W₁)` and
`Mor_C(U_•, W₂)`: a morphism in `C × C` is a pair of morphisms of `C`. -/
def diagYonedaProj : ∀ t : Bool, diagYoneda U W₁ W₂ ⟶ yonedaPairFam U W₁ W₂ t
  | false => { app _ := ↾fun x => x.1, naturality _ _ _ := rfl }
  | true => { app _ := ↾fun x => x.2, naturality _ _ _ := rfl }

/-- **In each degree the projections exhibit `Mor_{C × C}(u(U_•), (W₁, W₂))` as the product of
`Mor_C(U_•, W₁)` and `Mor_C(U_•, W₂)`**, a morphism `(U_n, U_n) ⟶ (W₁, W₂)` of `C × C` being
exactly a pair of morphisms `U_n ⟶ W₁` and `U_n ⟶ W₂` of `C`. -/
def isLimitDiagYonedaFan (n : SimplexCategoryᵒᵖ) :
    IsLimit (Fan.mk ((diagYoneda U W₁ W₂).obj n) fun t => (diagYonedaProj U W₁ W₂ t).app n) :=
  Fan.IsLimit.mk _ (fun s => ↾fun x => (s.proj false x, s.proj true x))
    (fun s t => by cases t <;> rfl)
    (fun s m hm => by
      ext x
      refine Prod.ext ?_ ?_
      · exact ConcreteCategory.congr_hom (hm false) x
      · exact ConcreteCategory.congr_hom (hm true) x)

/-- The unique map from `Mor_{C × C}(u(U_•), (W₁, W₂))` to the constant simplicial set on a
singleton. -/
def diagYonedaToPoint :
    diagYoneda U W₁ W₂ ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} where
  app _ := ↾fun _ => PUnit.unit

/-- **The point-resolution hypothesis of Tag 08Q9 is stable under the diagonal functor.** If
every simplicial set `Mor_C(U_•, W)` is homotopy equivalent to a singleton, then so is every
simplicial set `Mor_{C × C}(u(U_•), (W₁, W₂))`, because the latter is degreewise the product of
`Mor_C(U_•, W₁)` and `Mor_C(U_•, W₂)` and a product of two homotopy equivalences is a homotopy
equivalence (Tag 08Q4).

This is the step performed in the proof of Tag 08QC. -/
theorem isPointResolution_comp_diag (hU : IsPointResolution U) :
    IsPointResolution (U ⋙ Functor.diag C) := by
  rintro ⟨V₁, V₂⟩
  obtain ⟨f₁, hf₁⟩ := hU V₁
  obtain ⟨f₂, hf₂⟩ := hU V₂
  refine ⟨diagYonedaToPoint U V₁ V₂, ?_⟩
  have key := CategoryTheory.SimplicialObject.nonempty_homotopy_and_homotopyEquivalences_of_isLimit
    (C := Type u) (T := Bool) (X := yonedaPairFam U V₁ V₂)
    (Y := fun _ => (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1})
    (P := diagYoneda U V₁ V₂)
    (Q := (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1})
    (diagYonedaProj U V₁ V₂) (fun _ => 𝟙 _)
    (isLimitDiagYonedaFan U V₁ V₂)
    (fun _ => Fan.IsLimit.mk _ (fun _ => ↾fun _ => PUnit.unit) (fun _ _ => rfl)
      (fun _ _ _ => rfl))
    (a := fun t => match t with | false => f₁ | true => f₂)
    (b := fun t => match t with | false => f₁ | true => f₂)
    (f := diagYonedaToPoint U V₁ V₂) (g := diagYonedaToPoint U V₁ V₂)
    (fun _ => rfl) (fun _ => rfl)
  exact key.2.2 inferInstance fun t => by cases t <;> assumption

/-- **Tag 08Q9 on `C × C` for the diagonal image of a point resolution.** For every abelian
presheaf `ℱ` on `C × C` the homology `L_nπ_!` of `C × C` with coefficients `ℱ` is the homology
of the Moore complex of `ℱ(u(U_•))`, naturally in `ℱ`.

This is `Stacks.ChaoticSite.leftDerivedColimitNatIso` applied to the diagonal image, the
hypothesis being supplied by `Stacks.ChaoticSite.isPointResolution_comp_diag`. -/
def leftDerivedColimitNatIsoDiag (hU : IsPointResolution U) (n : ℕ) :
    (colim : ((C × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n ≅
      cosimplicialMooreComplex (U ⋙ Functor.diag C) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  leftDerivedColimitNatIso (U ⋙ Functor.diag C) (isPointResolution_comp_diag U hU) n

end Stacks.ChaoticSite

end
