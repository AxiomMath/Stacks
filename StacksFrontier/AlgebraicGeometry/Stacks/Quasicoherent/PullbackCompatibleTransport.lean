module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Transporting the sheaf condition along maps at the objects a fibre-product cover mentions

Let `{π i : X i ⟶ Y}` be a family of arrows admitting fibre products `W i j = X i ×_Y X j`.
`CategoryTheory.Presieve.isSheafFor_arrows_iff` reduces the sheaf condition for a presheaf `Q` and
that family to the statement that every compatible family of elements over the `X i` has a unique
amalgamation; and compatibility, which quantifies over an arbitrary test object of the category,
is implied by agreement on the `W i j` alone, since a cospan into `X i` and `X j` over `Y`
factors through the fibre product.

So the sheaf condition transports along maps given at `Y`, at the `X i` and at the `W i j`, with
no naturality anywhere else. This file records that transport, with each map asked for in the
weakest form the argument uses: a bijection over `Y`, an injection over each `X i`, and a bare
function over each `W i j`.

Why the weak form matters: a consumer which has a second presheaf `Q'` satisfying the sheaf
condition and an identification of `Q` with `Q'` that is only available over *some* objects of
the category cannot use a natural isomorphism of presheaves and must not pretend to have one.
That is the situation of the step of **Stacks 076T** assembled in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilySheafCondition.lean`:
hypothesis (b) of that lemma identifies the two presheaves only along arrows lying over a flat
morphism locally of finite presentation, and
`AlgebraicGeometry.Stack.flat_hom_pullback_overPost` and
`AlgebraicGeometry.Stack.locallyOfFinitePresentation_hom_pullback_overPost` certify that the
objects named here are exactly of that kind. Asking for a natural isomorphism over the whole
slice instead would be clause (b) of **Stacks 06WK**, which is strictly stronger than
hypothesis (b) of Stacks 076T.

## Main results

* `CategoryTheory.Presieve.Arrows.compatible_of_isPullback`: a family of elements agreeing on
  prescribed fibre products of the covering family is compatible.
* `CategoryTheory.Presieve.Arrows.existsUnique_amalgamation_of_maps`: **the sheaf condition
  transports along maps given at the objects a fibre-product cover mentions.**
* `CategoryTheory.Presieve.Arrows.isSheafFor_ofArrows_of_maps`: the same conclusion read back as
  `CategoryTheory.Presieve.IsSheafFor`.

## Implementation notes

The fibre products are taken as data — objects `W i j` with two projections and a
`CategoryTheory.IsPullback` square — rather than as `CategoryTheory.Limits.pullback`. A consumer
which has them as `CategoryTheory.Limits.pullback` passes
`CategoryTheory.IsPullback.of_hasPullback`; a consumer which has them in some other form is not
forced to transport. Keeping them abstract also keeps the statement free of the
`CategoryTheory.Limits.HasPullback` instance, which otherwise has to agree between the maps
supplied here and the hypotheses the consumer states about the same objects.

The three families of maps are not assumed to come from a single morphism of presheaves, and the
three compatibilities are stated as pointwise equalities of functions applied to a section rather
than as equalities of morphisms, because the maps of the consumer are not morphisms in the
category the presheaves take values in.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 00VM](https://stacks.math.columbia.edu/tag/00VM)
-/

@[expose] public section

open CategoryTheory Opposite

universe t v u

namespace CategoryTheory.Presieve.Arrows

variable {C : Type u} [Category.{v} C] {Q Q' : Cᵒᵖ ⥤ Type t} {Y : C} {I : Type*} {X : I → C}
  (π : (i : I) → X i ⟶ Y) {W : I → I → C} (pr₁ : (i j : I) → W i j ⟶ X i)
  (pr₂ : (i j : I) → W i j ⟶ X j) (hW : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (π i) (π j))

include hW in
/-- **A family of elements agreeing on prescribed fibre products of a covering family is
compatible.** A cospan into `X i` and `X j` whose composites to `Y` agree factors through the
fibre product `X i ×_Y X j`, so agreement there is agreement against every test object. -/
theorem compatible_of_isPullback (y : (i : I) → Q.obj (op (X i)))
    (hy : ∀ i j, Q.map (pr₁ i j).op (y i) = Q.map (pr₂ i j).op (y j)) :
    Compatible Q π y := by
  intro i j Z gi gj hg
  have h₁ : Q.map gi.op (y i) =
      Q.map ((hW i j).lift gi gj hg).op (Q.map (pr₁ i j).op (y i)) := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, (hW i j).lift_fst]
  have h₂ : Q.map gj.op (y j) =
      Q.map ((hW i j).lift gi gj hg).op (Q.map (pr₂ i j).op (y j)) := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, (hW i j).lift_snd]
  rw [h₁, h₂, hy i j]

include hW in
/-- **The sheaf condition transports along maps given at the objects a fibre-product cover
mentions.**

Let `{π i : X i ⟶ Y}` be a family of arrows with prescribed fibre products `W i j`, and let `Q`,
`Q'` be presheaves of types. Suppose given a bijective map `θ` of the sections over `Y`, an
injective map `θX i` of the sections over each `X i` and an arbitrary map `θP i j` of the sections
over each `W i j`, commuting with restriction along `π i`, along `pr₁ i j` and along `pr₂ i j`
respectively. Then, if every compatible family of elements of `Q'` has a unique amalgamation, so
does every compatible family of elements of `Q`.

Nothing is assumed about `Q` and `Q'` at any other object of the category, and the three
families of maps are not assumed to be the components of a morphism of presheaves. -/
theorem existsUnique_amalgamation_of_maps
    (θ : Q.obj (op Y) → Q'.obj (op Y)) (hθ : Function.Bijective θ)
    (θX : (i : I) → Q.obj (op (X i)) → Q'.obj (op (X i)))
    (hθX : ∀ i, Function.Injective (θX i))
    (θP : (i j : I) → Q.obj (op (W i j)) → Q'.obj (op (W i j)))
    (hπ : ∀ (i : I) (s : Q.obj (op Y)), θX i (Q.map (π i).op s) = Q'.map (π i).op (θ s))
    (h₁ : ∀ (i j : I) (s : Q.obj (op (X i))),
      θP i j (Q.map (pr₁ i j).op s) = Q'.map (pr₁ i j).op (θX i s))
    (h₂ : ∀ (i j : I) (s : Q.obj (op (X j))),
      θP i j (Q.map (pr₂ i j).op s) = Q'.map (pr₂ i j).op (θX j s))
    (h' : ∀ y : (i : I) → Q'.obj (op (X i)), Compatible Q' π y →
      ∃! s, ∀ i, Q'.map (π i).op s = y i)
    (y : (i : I) → Q.obj (op (X i))) (hy : Compatible Q π y) :
    ∃! s, ∀ i, Q.map (π i).op s = y i := by
  have hy' : Compatible Q' π fun i => θX i (y i) := by
    refine compatible_of_isPullback π pr₁ pr₂ hW _ fun i j => ?_
    rw [← h₁ i j, ← h₂ i j, hy i j (W i j) (pr₁ i j) (pr₂ i j) (hW i j).w]
  obtain ⟨s', hs', huniq'⟩ := h' _ hy'
  obtain ⟨t, ht⟩ := hθ.surjective s'
  refine ⟨t, fun i => hθX i ?_, fun s₂ hs₂ => ?_⟩
  · rw [hπ i, ht, hs' i]
  · have hθs : θ s₂ = s' := huniq' _ fun i => by rw [← hπ i, hs₂ i]
    exact hθ.injective (hθs.trans ht.symm)

include hW in
/-- **The sheaf condition for a family of arrows transports along maps given at the objects a
fibre-product cover mentions.**
`CategoryTheory.Presieve.Arrows.existsUnique_amalgamation_of_maps` read back through
`CategoryTheory.Presieve.isSheafFor_arrows_iff`. -/
theorem isSheafFor_ofArrows_of_maps
    (θ : Q.obj (op Y) → Q'.obj (op Y)) (hθ : Function.Bijective θ)
    (θX : (i : I) → Q.obj (op (X i)) → Q'.obj (op (X i)))
    (hθX : ∀ i, Function.Injective (θX i))
    (θP : (i j : I) → Q.obj (op (W i j)) → Q'.obj (op (W i j)))
    (hπ : ∀ (i : I) (s : Q.obj (op Y)), θX i (Q.map (π i).op s) = Q'.map (π i).op (θ s))
    (h₁ : ∀ (i j : I) (s : Q.obj (op (X i))),
      θP i j (Q.map (pr₁ i j).op s) = Q'.map (pr₁ i j).op (θX i s))
    (h₂ : ∀ (i j : I) (s : Q.obj (op (X j))),
      θP i j (Q.map (pr₂ i j).op s) = Q'.map (pr₂ i j).op (θX j s))
    (h' : Presieve.IsSheafFor Q' (Presieve.ofArrows X π)) :
    Presieve.IsSheafFor Q (Presieve.ofArrows X π) :=
  (Presieve.isSheafFor_arrows_iff Q π).2
    (existsUnique_amalgamation_of_maps π pr₁ pr₂ hW θ hθ θX hθX θP hπ h₁ h₂
      ((Presieve.isSheafFor_arrows_iff Q' π).1 h'))

end CategoryTheory.Presieve.Arrows

end
