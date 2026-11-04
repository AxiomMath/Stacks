module

public import StacksFrontier.CategoryTheory.TwoYoneda.PullbackComparison

/-!
# The 2-Yoneda lemma as a choice of representing functor

Let `p : S ⥤ C` be fibred in groupoids and let `U` be an object of `C`. The 2-Yoneda lemma
(`CategoryTheory.Functor.twoYonedaEvaluation_isEquivalence`, Stacks 004B) says that evaluating a
functor over `C` on the slice `C/U` at the terminal object `(U, 𝟙 U)` is an equivalence onto the
fibre of `p` over `U`. This file records the two halves of that equivalence as *data* usable in a
proof: a chosen representing functor for an object of the fibre, together with the comparison of
its value at the terminal object with that object, and a chosen 2-morphism representing a given
morphism of fibre objects, together with the computation of its component at the terminal object.

Both are built from the explicit constructions behind the 2-Yoneda lemma rather than from the
abstract equivalence, so the representing functor is `CategoryTheory.Functor.TwoYoneda.liftBased`,
assembled from the chosen cartesian lifts, and the comparison is the chosen lift at `𝟙 U`.

## Main definitions

* `CategoryTheory.Functor.TwoYoneda.liftBasedEvaluationIso`: the value of the representing
  functor of an object of the fibre, compared with that object.
* `CategoryTheory.Functor.TwoYoneda.hom₂OfFiberHom`: the 2-morphism of functors over `C`
  representing a morphism of the fibre objects they evaluate to.

## Main results

* `CategoryTheory.Functor.TwoYoneda.hom₂OfFiberHom_app_unit`: the component of that 2-morphism
  at the terminal object is the given morphism of fibre objects.

## Implementation notes

The fibre of a category fibred in groupoids is a groupoid, so the comparison arrow of
`liftBasedEvaluationIso` is invertible; that is how `CategoryTheory.Functor.Fiber.homMk` of the
chosen lift becomes an isomorphism. The chosen lift is stated at `𝟙 U` rather than at
`(Over.mk (𝟙 U)).hom`, which is only semireducibly the same arrow — the same device the proof of
`CategoryTheory.Functor.twoYonedaEvaluation_essSurj` uses.

The 2-morphism of `hom₂OfFiberHom` is the preimage under full faithfulness of evaluation, so its
component at the terminal object is computed by
`CategoryTheory.Functor.TwoYoneda.twoYonedaEvaluation_preimage_app` rather than by repeating that
computation.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor.TwoYoneda

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]

/-- **Stacks 004B**, essential surjectivity as data. The functor over `C` on the slice `C/U`
assembled from the chosen cartesian lifts of an object `x` of the fibre of `p` over `U` evaluates
at the terminal object to an object canonically isomorphic to `x`: the chosen lift at `𝟙 U` is an
arrow of the fibre, and the fibre of a category fibred in groupoids is a groupoid. -/
@[stacks 004B "essential surjectivity of evaluation, as data"]
noncomputable def liftBasedEvaluationIso (p : S ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C)
    (x : p.Fiber U) :
    (Functor.twoYonedaEvaluation p U).obj (liftBased p hp U x) ≅ x := by
  have := hp.fiber_isGroupoid U
  have : p.IsHomLift (𝟙 U) (chosenLift p hp U x (Over.mk (𝟙 U))).φ :=
    (chosenLift p hp U x (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift
  have e := asIso (Functor.Fiber.homMk p U (chosenLift p hp U x (Over.mk (𝟙 U))).φ)
  exact e

variable (p : S ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C)
  {G G' : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}

/-- **Stacks 004B**, fullness as data. The 2-morphism of functors over `C` on the slice `C/U`
representing a morphism of the fibre objects they evaluate to. -/
@[stacks 004B "fullness of evaluation, as data"]
noncomputable def hom₂OfFiberHom
    (φ : (Functor.twoYonedaEvaluation p U).obj G ⟶ (Functor.twoYonedaEvaluation p U).obj G') :
    G ⟶ G' :=
  have := Functor.twoYonedaEvaluation_full p hp U
  have := Functor.twoYonedaEvaluation_faithful p hp U
  (Functor.FullyFaithful.ofFullyFaithful (Functor.twoYonedaEvaluation p U)).preimage φ

/-- The component at the terminal object of the 2-morphism representing a morphism of fibre
objects is that morphism. -/
theorem hom₂OfFiberHom_app_unit
    (φ : (Functor.twoYonedaEvaluation p U).obj G ⟶ (Functor.twoYonedaEvaluation p U).obj G') :
    (hom₂OfFiberHom p hp U φ).app (Over.mk (𝟙 U)) = Functor.Fiber.fiberInclusion.map φ :=
  twoYonedaEvaluation_preimage_app p U (Functor.twoYonedaEvaluation_isEquivalence p hp U) φ

/-- Evaluation sends the 2-morphism representing a morphism of fibre objects to that
morphism. -/
@[simp]
theorem twoYonedaEvaluation_map_hom₂OfFiberHom
    (φ : (Functor.twoYonedaEvaluation p U).obj G ⟶ (Functor.twoYonedaEvaluation p U).obj G') :
    (Functor.twoYonedaEvaluation p U).map (hom₂OfFiberHom p hp U φ) = φ :=
  Functor.Fiber.hom_ext
    ((Functor.twoYonedaEvaluation_map p U (hom₂OfFiberHom p hp U φ)).trans
      (hom₂OfFiberHom_app_unit p hp U φ))

end CategoryTheory.Functor.TwoYoneda

end
