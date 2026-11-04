module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibrePullback
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibresDiagonal

/-!
# The split fibre of a diagonal, read componentwise

Let `G : 𝒮 ⥤ 𝒮'` be a functor strictly over a base category `𝒞` and let
`Δ_G : 𝒮 ⥤ 𝒮 ×_{G, 𝒮', G} 𝒮` be its diagonal (`CategoryTheory.TwoFibreProductOver.diagonal`).
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibresDiagonal` identifies the functor induced by
`Δ_G` on the fibres over an object `U` of `𝒞` with the diagonal of the induced functor `G_U`, on
the nose. The *split* fibres of Stacks 004A need one thing more: a morphism of the split fibre
over `V` is a morphism between *chosen pullbacks*, and reading it componentwise conjugates it by
the comparisons
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` of the chosen
pullbacks of the 2-fibre product with those of its factors. This file identifies those
comparisons, on the image of the diagonal, with the base-change comparison
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` of `Δ_G` itself.

Both comparisons are pinned by a factorization through one and the same cartesian lift of
`h : V ⟶ U` -- the chosen lift at the object of `𝒮_U`, through which the `𝒮`-component of the
chosen lift in the 2-fibre product factors -- so they agree by the uniqueness statement
`CategoryTheory.Functor.fiber_hom_ext_of_cartesian`. This is the whole mathematical content
behind the identity, in the split model, between the comparison of the split fibre of a 2-fibre
product and the diagonal of the split fibres.

## Main results

* `CategoryTheory.TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_hom_fst` and
  `CategoryTheory.TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_hom_snd`: the two
  components of the base-change comparison of the diagonal are the two chosen-pullback
  comparisons of the 2-fibre product.
* `CategoryTheory.TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_inv_fst` and
  `CategoryTheory.TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_inv_snd`: the same
  for the inverses, which is what conjugation needs.

## Implementation notes

The two comparisons live in fibres that are only *definitionally* equal: the target of the
`𝒮`-component of `CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` for `Δ_G` is
the `𝒮`-component of the fibre of the diagonal, while the target of
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` is the chosen
pullback of the `𝒮`-component. The statements are therefore elaborated at default transparency
and the proofs are given in term mode, with the two factorizations supplied as `have`s whose
stated types are the ones the goal needs; `rw` cannot be used, because the chosen cartesian lifts
the two factorizations mention differ by a proof argument.

## References

* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ u₁ u₂ u₃

attribute [local instance_reducible] diagonal

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  {𝒮' : Type u₃} [Category.{v₃} 𝒮']
  (p𝒮 : 𝒮 ⥤ 𝒞) (p𝒮' : 𝒮' ⥤ 𝒞) (G : 𝒮 ⥤ 𝒮') [p𝒮.IsFibered] [p𝒮'.IsFibered]
  [(structureFunctor p𝒮 p𝒮 p𝒮' G G).IsFibered]
  {hG : G ⋙ p𝒮' = p𝒮}
  (hΔ : Functor.IsFibredOneMorphism p𝒮 (structureFunctor p𝒮 p𝒮 p𝒮' G G) (diagonal hG))
  (h𝒮 : p𝒮.IsFiberedInGroupoids) {U V : 𝒞} (x : p𝒮.Fiber U) (h : V ⟶ U)

omit [p𝒮.IsFibered] [p𝒮'.IsFibered] [(structureFunctor p𝒮 p𝒮 p𝒮' G G).IsFibered] in
/-- **The two components of the fibre of the diagonal on a morphism are that morphism.** This is
`CategoryTheory.TwoFibreProductOver.fiberFunctor_diagonal_comp_toFiberPullback` read on a single
morphism, in the spelling the comparison out of a split fibre produces. -/
lemma toFiberPullback_map_fiberFunctorOfCompEq_map_fst {y y' : p𝒮.Fiber V} (β : y ⟶ y') :
    ((toFiberPullback p𝒮 p𝒮 p𝒮' G G hG hG V).map
        ((Functor.fiberFunctorOfCompEq hΔ.comp_eq V).map β)).fst = β := rfl

omit [p𝒮.IsFibered] [p𝒮'.IsFibered] [(structureFunctor p𝒮 p𝒮 p𝒮' G G).IsFibered] in
/-- The `𝒴`-side of
`CategoryTheory.TwoFibreProductOver.toFiberPullback_map_fiberFunctorOfCompEq_map_fst`. -/
lemma toFiberPullback_map_fiberFunctorOfCompEq_map_snd {y y' : p𝒮.Fiber V} (β : y ⟶ y') :
    ((toFiberPullback p𝒮 p𝒮 p𝒮' G G hG hG V).map
        ((Functor.fiberFunctorOfCompEq hΔ.comp_eq V).map β)).snd = β := rfl

omit [p𝒮.IsFibered] [p𝒮'.IsFibered] [(structureFunctor p𝒮 p𝒮 p𝒮' G G).IsFibered] in
/-- **The comparison isomorphism of the fibre of the diagonal is an identity**: the triple
`Δ_G x` has `𝟙` for its comparison isomorphism, and Stacks 02XI keeps it. -/
lemma toFiberPullback_obj_fiberFunctorOfCompEq_obj_iso_hom (y : p𝒮.Fiber V) :
    ((toFiberPullback p𝒮 p𝒮 p𝒮' G G hG hG V).obj
        ((Functor.fiberFunctorOfCompEq hΔ.comp_eq V).obj y)).iso.hom = 𝟙 _ := rfl

omit [p𝒮.IsFibered] [(structureFunctor p𝒮 p𝒮 p𝒮' G G).IsFibered] in
/-- **The chosen pullback of the comparison isomorphism of the fibre of a diagonal is an
identity**, that comparison isomorphism being one by
`CategoryTheory.TwoFibreProductOver.toFiberPullback_obj_fiberFunctorOfCompEq_obj_iso_hom`. This
is the object half of the identity between the split fibre of a diagonal and the diagonal of the
split fibres, isolated so that the definitional unfolding happens here, over abstract categories,
rather than inside the goal it is used in. -/
lemma pullbackFiberHom_toFiberPullback_obj_diagonal_iso_hom (y : p𝒮.Fiber U) (h : V ⟶ U) :
    Functor.pullbackFiberHom
        ((toFiberPullback p𝒮 p𝒮 p𝒮' G G hG hG U).obj
          ((Functor.fiberFunctorOfCompEq hΔ.comp_eq U).obj y)).iso.hom h =
      𝟙 (Functor.pullbackFiber p𝒮' ((Functor.fiberMap p𝒮 p𝒮' G hG U).obj y) h) :=
  Functor.pullbackFiberHom_id h

omit [p𝒮'.IsFibered] in
/-- **The `𝒮`-component of the base-change comparison of the diagonal is the chosen-pullback
comparison of the 2-fibre product.** Both are morphisms of the fibre `𝒮_V` whose composite with
the chosen cartesian lift of `h` at `x` is the `𝒮`-component of the chosen cartesian lift of `h`
at the image of `x` under the diagonal, so they agree by cartesian uniqueness. -/
lemma toFiberPullback_map_mapPullbackFiberIso_hom_fst :
    ((toFiberPullback p𝒮 p𝒮 p𝒮' G G hG hG V).map
          (hΔ.mapPullbackFiberIso x h).hom).fst =
      (pullbackFiberFstIsoOfFiberedInGroupoids p𝒮 p𝒮 p𝒮' G G hG hG
        ((Functor.fiberFunctorOfCompEq hΔ.comp_eq U).obj x) h h𝒮).hom := by
  refine Functor.fiber_hom_ext_of_cartesian h (Functor.IsPreFibered.pullbackMap x.2 h)
    (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 h) _ _ ?_
  exact (congrArg Hom.a (hΔ.mapPullbackFiberIso_hom_fac x h)).trans
    (pullbackFiberFstIsoOfFiberedInGroupoids_hom_fac p𝒮 p𝒮 p𝒮' G G hG hG
      ((Functor.fiberFunctorOfCompEq hΔ.comp_eq U).obj x) h h𝒮).symm

omit [p𝒮'.IsFibered] in
/-- **The `𝒮`-component of the inverse base-change comparison of the diagonal is the inverse
chosen-pullback comparison.** Both are inverse to the morphism of
`CategoryTheory.TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_hom_fst`. -/
lemma toFiberPullback_map_mapPullbackFiberIso_inv_fst :
    ((toFiberPullback p𝒮 p𝒮 p𝒮' G G hG hG V).map
          (hΔ.mapPullbackFiberIso x h).inv).fst =
      (pullbackFiberFstIsoOfFiberedInGroupoids p𝒮 p𝒮 p𝒮' G G hG hG
        ((Functor.fiberFunctorOfCompEq hΔ.comp_eq U).obj x) h h𝒮).inv := by
  refine (Iso.inv_ext ?_).symm
  rw [← toFiberPullback_map_mapPullbackFiberIso_hom_fst p𝒮 p𝒮' G hΔ h𝒮 x h,
    ← CategoricalPullback.comp_fst, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
    CategoricalPullback.id_fst]

omit [p𝒮'.IsFibered] in
/-- **The second component of the base-change comparison of the diagonal is the second
chosen-pullback comparison**, by the argument of
`CategoryTheory.TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_hom_fst` on the other
side: the two components of the diagonal coincide. -/
lemma toFiberPullback_map_mapPullbackFiberIso_hom_snd :
    ((toFiberPullback p𝒮 p𝒮 p𝒮' G G hG hG V).map
          (hΔ.mapPullbackFiberIso x h).hom).snd =
      (pullbackFiberSndIsoOfFiberedInGroupoids p𝒮 p𝒮 p𝒮' G G hG hG
        ((Functor.fiberFunctorOfCompEq hΔ.comp_eq U).obj x) h h𝒮).hom := by
  refine Functor.fiber_hom_ext_of_cartesian h (Functor.IsPreFibered.pullbackMap x.2 h)
    (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 h) _ _ ?_
  exact (congrArg Hom.b (hΔ.mapPullbackFiberIso_hom_fac x h)).trans
    (pullbackFiberSndIsoOfFiberedInGroupoids_hom_fac p𝒮 p𝒮 p𝒮' G G hG hG
      ((Functor.fiberFunctorOfCompEq hΔ.comp_eq U).obj x) h h𝒮).symm

omit [p𝒮'.IsFibered] in
/-- **The second component of the inverse base-change comparison of the diagonal is the second
inverse chosen-pullback comparison.** -/
lemma toFiberPullback_map_mapPullbackFiberIso_inv_snd :
    ((toFiberPullback p𝒮 p𝒮 p𝒮' G G hG hG V).map
          (hΔ.mapPullbackFiberIso x h).inv).snd =
      (pullbackFiberSndIsoOfFiberedInGroupoids p𝒮 p𝒮 p𝒮' G G hG hG
        ((Functor.fiberFunctorOfCompEq hΔ.comp_eq U).obj x) h h𝒮).inv := by
  refine (Iso.inv_ext ?_).symm
  rw [← toFiberPullback_map_mapPullbackFiberIso_hom_snd p𝒮 p𝒮' G hΔ h𝒮 x h,
    ← CategoricalPullback.comp_snd, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
    CategoricalPullback.id_snd]

end CategoryTheory.TwoFibreProductOver

end
