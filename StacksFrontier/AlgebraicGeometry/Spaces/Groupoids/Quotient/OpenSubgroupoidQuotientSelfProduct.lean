module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientHom
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverMapBaseSurjective

/-!
# Self 2-fibre products over the quotient stack of an open subgroupoid

Let `φ : (U, P, …) ⟶ (U, R, …)` be a morphism of groupoids in algebraic spaces whose arrow map is a
monomorphism — the inclusion of an open subgroupoid, say — and let `[φ] : [U/P] ⟶ [U/R]` be the
induced 1-morphism of Stacks 046Q. Fix a class of *good* points of the object space, stable under
pullback, such that every arrow of `R` between the images of two good points comes from an arrow of
`P` between the points themselves. For a 1-morphism `q : 𝒯 ⟶ [U/P]` all of whose objects are
isomorphic to objects presented by good points, the comparison
```
  𝒯 ×_{[U/P]} 𝒯 ⟶ 𝒯 ×_{[U/R]} 𝒯
```
obtained by postcomposing both legs with `[φ]` is an equivalence.

In the proof of **Stacks 0DU5** the good points are those factoring through a point
`u : Spec κ(u) ⟶ U`, the class is the open subgroupoid `P` of a strong splitting over `u` (which
contains every arrow of `R` with source and target `u`), and `q` is `Spec κ(u) ⟶ U ⟶ [U/P]`. The
conclusion is the source's "`u ×_𝒰 u ⟶ u ×_𝒳 u` is an isomorphism", the hypothesis of Stacks 0DTI.

## Main results

* `AlgebraicGeometry.Stack.quotientStackMap_map_surjective_of_good`: `[φ]` is surjective on the
  morphisms between two objects presented by good points.
* `AlgebraicGeometry.Stack.isEquivalence_mapBase_quotientStackMap`: the comparison of self
  2-fibre products is an equivalence.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 0DTI](https://stacks.math.columbia.edu/tag/0DTI)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite

namespace AlgebraicGeometry.Stack

universe u vT uT

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **`[φ]` is surjective on the morphisms between two objects presented by good points.** With
`Good` and the arrow condition as in
`AlgebraicGeometry.Stack.isEquivalence_mapBase_quotientStackMap`, if `Z₁` and `Z₂` are isomorphic
to objects of `[U/P]` presented by good points, then `[φ]` is surjective on the morphisms
`Z₁ ⟶ Z₂`. -/
theorem quotientStackMap_map_surjective_of_good {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (Good : ∀ T : BigFppfOver C S hS, G.objects.obj.obj (op T) → Prop)
    (hpull : ∀ {T T' : BigFppfOver C S hS} (g : T ⟶ T') (y : G.objects.obj.obj (op T')),
      Good T' y → Good T (G.objects.obj.map g.op y))
    (harrow : ∀ (T : BigFppfOver C S hS) (x y : G.objects.obj.obj (op T)), Good T x → Good T y →
      ∀ b : H.arrows.obj.obj (op T),
        H.toGroupoidInFunctors.source.app (op T) b =
            φ.toGroupoidHom.mapObjects.app (op T) x →
          H.toGroupoidInFunctors.target.app (op T) b =
            φ.toGroupoidHom.mapObjects.app (op T) y →
          ∃ a : G.arrows.obj.obj (op T),
            G.toGroupoidInFunctors.source.app (op T) a = x ∧
            G.toGroupoidInFunctors.target.app (op T) a = y ∧
            φ.toGroupoidHom.mapArrows.app (op T) a = b)
    {Z₁ Z₂ : (quotientStack G).obj}
    (h₁ : ∃ X : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj,
      Good X.base X.fiber ∧ Nonempty (Z₁ ≅ (pointwiseToQuotientStack G).obj X))
    (h₂ : ∃ X : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj,
      Good X.base X.fiber ∧ Nonempty (Z₂ ≅ (pointwiseToQuotientStack G).obj X)) :
    Function.Surjective ((quotientStackMap φ).toFunctor.map : (Z₁ ⟶ Z₂) → _) := by
  obtain ⟨X, hX, ⟨eX⟩⟩ := h₁
  obtain ⟨Y, hY, ⟨eY⟩⟩ := h₂
  refine Functor.map_surjective_of_iso _ eX.symm eY.symm ?_
  refine quotientStackMap_map_surjective φ ?_
  intro g r hr₁ hr₂
  exact harrow X.base X.fiber _ hX (hpull g Y.fiber hY) r hr₁ hr₂

/-- **The comparison of self 2-fibre products along `[φ]` is an equivalence when every object of
the leg is presented by a good point.** Let `φ : G ⟶ H` be a morphism of groupoids in algebraic
spaces whose arrow map is a monomorphism, and let `Good` be a class of points of the object space
of `G` over test objects, stable under pullback, such that every arrow of `H` over `T` between the
images of two good points over `T` is the image of an arrow of `G` between them. Let
`q : 𝒯 ⥤ [U/P]` be a functor every object of which is isomorphic to the object presented by a good
point. Then postcomposing both legs of `𝒯 ×_{[U/P]} 𝒯` with `[φ]` is an equivalence onto
`𝒯 ×_{[U/R]} 𝒯`. -/
theorem isEquivalence_mapBase_quotientStackMap {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) (hmono : Mono φ.toGroupoidHom.mapArrows)
    (Good : ∀ T : BigFppfOver C S hS, G.objects.obj.obj (op T) → Prop)
    (hpull : ∀ {T T' : BigFppfOver C S hS} (g : T ⟶ T') (y : G.objects.obj.obj (op T')),
      Good T' y → Good T (G.objects.obj.map g.op y))
    (harrow : ∀ (T : BigFppfOver C S hS) (x y : G.objects.obj.obj (op T)), Good T x → Good T y →
      ∀ b : H.arrows.obj.obj (op T),
        H.toGroupoidInFunctors.source.app (op T) b =
            φ.toGroupoidHom.mapObjects.app (op T) x →
          H.toGroupoidInFunctors.target.app (op T) b =
            φ.toGroupoidHom.mapObjects.app (op T) y →
          ∃ a : G.arrows.obj.obj (op T),
            G.toGroupoidInFunctors.source.app (op T) a = x ∧
            G.toGroupoidInFunctors.target.app (op T) a = y ∧
            φ.toGroupoidHom.mapArrows.app (op T) a = b)
    {𝒯 : Type uT} [Category.{vT} 𝒯] {pT : 𝒯 ⥤ BigFppfOver C S hS}
    (q : 𝒯 ⥤ (quotientStack G).obj)
    (hq : ∀ a : 𝒯, ∃ X : (presheafOfGroupoids
        (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj,
      Good X.base X.fiber ∧ Nonempty (q.obj a ≅ (pointwiseToQuotientStack G).obj X)) :
    (TwoFibreProductOver.mapBase (pT := pT) (p𝒜 := pT) q q (quotientStackMap φ).toFunctor
      (quotientStackMap φ).w).IsEquivalence := by
  have := faithful_quotientStackMap_of_mono φ hmono
  have hsurj : ∀ a b : 𝒯, Function.Surjective ((quotientStackMap φ).toFunctor.map :
      (q.obj a ⟶ q.obj b) → _) := fun a b =>
    quotientStackMap_map_surjective_of_good φ Good hpull harrow (hq a) (hq b)
  exact TwoFibreProductOver.isEquivalence_mapBase_of_surjective _
    (fun a b => hsurj a b) (fun a b => hsurj b a)

end AlgebraicGeometry.Stack

end
