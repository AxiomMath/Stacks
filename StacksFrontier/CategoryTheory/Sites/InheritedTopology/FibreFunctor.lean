module

public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulDescent

/-! # The functor induced on fibres by a 1-morphism of fibred categories

Let `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be fibred categories over `𝒞` and let `F : 𝒳 ⥤ 𝒴` be a
1-morphism of fibred categories over `𝒞`. For every object `U` of `𝒞` it induces a functor
`F_U : 𝒳_U ⥤ 𝒴_U` on the fibres, `CategoryTheory.Functor.Fiber.mapOfComp`. This file proves:

* it is faithful, respectively full, as soon as `F` is — neither direction needs the fibres to
  be groupoids, which is what Stacks 003Z assumes;
* the comparison isomorphism `F_V (f^* x) ≅ f^* (F_U x)` of
  `CategoryTheory.Functor.mapPullbackFiberIso'` turns a contraction of iterated chosen
  pullbacks in `𝒳` into the corresponding contraction in `𝒴`.

## Main results

* `CategoryTheory.Functor.Fiber.faithful_mapOfComp`,
  `CategoryTheory.Functor.Fiber.full_mapOfComp`;
* `CategoryTheory.Functor.mapPullbackFiberIso'_hom_fac`,
  `CategoryTheory.Functor.mapPullbackFiberIso'_inv_fac`;
* `CategoryTheory.Functor.mapOfComp_map_pullbackFiberCompIso'`, the compatibility with
  contraction of iterated chosen pullbacks.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ### Faithfulness and fullness on fibres -/

section FullyFaithful

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]
variable {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p)

/-- The functor induced on the fibre over `U` by a faithful functor over `𝒞` is faithful. -/
lemma Fiber.faithful_mapOfComp [F.Faithful] (U : 𝒞) : (Fiber.mapOfComp p q F hF U).Faithful where
  map_injective {a b} φ ψ h := by
    exact Fiber.hom_ext (F.map_injective (congrArg Fiber.fiberInclusion.map h))

-- The chosen pullbacks and the inclusion of a fibre are semireducible, so the endpoints of the
-- composites below agree only once they unfold.
set_option backward.isDefEq.respectTransparency false in
/-- The functor induced on the fibre over `U` by a full functor over `𝒞` is full. -/
lemma Fiber.full_mapOfComp [F.Full] (U : 𝒞) : (Fiber.mapOfComp p q F hF U).Full where
  map_surjective {a b} ψ := by
    obtain ⟨χ, hχ⟩ := F.map_surjective (Fiber.fiberInclusion.map ψ)
    have hlift : p.IsHomLift (𝟙 U) χ := by
      refine IsHomLift.of_fac' p (𝟙 U) χ a.2 b.2 ?_
      rw [map_eq_of_comp_eq p q F hF χ, hχ, IsHomLift.fac' q (𝟙 U) (Fiber.fiberInclusion.map ψ)]
      simp
    exact ⟨⟨χ, hlift⟩, Fiber.hom_ext hχ⟩

end FullyFaithful

/-! ### The comparison isomorphism and iterated chosen pullbacks -/

section MapPullbackFiber

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]
variable {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} [p.IsFibered] [q.IsFibered] {F : 𝒳 ⥤ 𝒴}
variable (hF : IsFibredOneMorphism p q F)

/-- The defining factorization of `CategoryTheory.Functor.mapPullbackFiberIso'`: it carries the
`F`-image of the chosen cartesian lift to the chosen cartesian lift of the `F`-image. -/
@[reassoc (attr := simp)]
lemma mapPullbackFiberIso'_hom_fac {U : 𝒞} (y : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    Fiber.fiberInclusion.map (mapPullbackFiberIso' hF y f).hom ≫
        F.map (IsPreFibered.pullbackMap y.2 f) =
      IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF.comp_eq U).obj y).2 f :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

-- The chosen pullbacks and the inclusion of a fibre are semireducible, so the endpoints of the
-- composites below agree only once they unfold.
set_option backward.isDefEq.respectTransparency false in
/-- The factorization of the inverse of `CategoryTheory.Functor.mapPullbackFiberIso'`. -/
@[reassoc (attr := simp)]
lemma mapPullbackFiberIso'_inv_fac {U : 𝒞} (y : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    Fiber.fiberInclusion.map (mapPullbackFiberIso' hF y f).inv ≫
        IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF.comp_eq U).obj y).2 f =
      F.map (IsPreFibered.pullbackMap y.2 f) :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

-- The chosen pullbacks and the inclusion of a fibre are semireducible, so the endpoints of the
-- composites below agree only once they unfold.
set_option backward.isDefEq.respectTransparency false in
/-- The induced functor on fibres carries the contraction of an iterated chosen pullback in `𝒳`
to the contraction in `𝒴`, up to the comparison isomorphisms
`CategoryTheory.Functor.mapPullbackFiberIso'`. -/
lemma mapOfComp_map_pullbackFiberCompIso' {T V Z : 𝒞} (z : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V)
    (b : Z ⟶ T) (hb : ε ≫ f = b) :
    (Fiber.mapOfComp p q F hF.comp_eq Z).map (pullbackFiberCompIso' z f ε b hb).hom ≫
        (mapPullbackFiberIso' hF z b).inv =
      (mapPullbackFiberIso' hF (pullbackFiber p z f) ε).inv ≫
        pullbackFiberHom (mapPullbackFiberIso' hF z f).inv ε ≫
        (pullbackFiberCompIso' ((Fiber.mapOfComp p q F hF.comp_eq T).obj z) f ε b hb).hom := by
  refine fiber_hom_ext_of_cartesian b
    (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF.comp_eq T).obj z).2 b)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  have hleft : Fiber.fiberInclusion.map
        ((Fiber.mapOfComp p q F hF.comp_eq Z).map (pullbackFiberCompIso' z f ε b hb).hom) =
      F.map (Fiber.fiberInclusion.map (pullbackFiberCompIso' z f ε b hb).hom) := rfl
  simp only [Functor.map_comp, Category.assoc, hleft, mapPullbackFiberIso'_inv_fac,
    pullbackFiberCompIso'_hom_fac, pullbackFiberHom_fac_assoc,
    mapPullbackFiberIso'_inv_fac_assoc]
  rw [← F.map_comp, pullbackFiberCompIso'_hom_fac, F.map_comp]

end MapPullbackFiber

end CategoryTheory.Functor
