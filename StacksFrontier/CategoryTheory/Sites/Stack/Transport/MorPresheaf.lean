module

public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.PullbackComparison

/-!
# The morphism presheaves are identified by an equivalence over the base

Let `e : BasedCategory.Equivalence 𝒳 𝒴` be an equivalence of categories over `𝒞`, with both sides
fibred, and let `F` be its forward functor. For objects `x, y` of a fibre of `𝒳`, the sections of
`Mor(x, y)`, taken in `𝒳`, are in natural bijection with those of `Mor(F x, F y)`, taken in `𝒴`.
Consequently, if the presheaves `Mor(x, y)` of `𝒳` are sheaves, so are those of `𝒴`.

## Main definitions

* `CategoryTheory.BasedCategory.Equivalence.morSectionEquiv`, the bijection on sections over `g`.
* `CategoryTheory.BasedCategory.Equivalence.morPresheafIso`, the identification of the morphism
  presheaf of `x, y` with that of `F x, F y`, for two categories over `𝒞` in the same universes.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.morSectionEquiv_naturality`, the naturality of the
  bijection on sections in the arrow of `𝒞/U`.
* `CategoryTheory.BasedCategory.Equivalence.isMorSheaf`: if the morphism presheaves of `𝒳` are
  sheaves, so are those of `𝒴`.

## Implementation notes

`𝒳` and `𝒴` live in independent universes, so `Mor(x, y)` and `Mor(F x, F y)` take values in two
different `Type` universes and are not objects of one functor category. The identification is
therefore a bijection on sections, natural in the arrow of `𝒞/U`; when the two hom universes
agree it assembles into the isomorphism of presheaves
`CategoryTheory.BasedCategory.Equivalence.morPresheafIso`.

## References

* [Stacks Project, Tag 042V](https://stacks.math.columbia.edu/tag/042V)
-/

@[expose] public section

-- The transports below relate `p` and `𝒴.p` through `BasedFunctor.comp`, whose instance
-- arguments are only found after unfolding the composite.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

namespace BasedCategory.Equivalence

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
  (e : BasedCategory.Equivalence 𝒳 𝒴)

include e

variable [𝒳.p.IsFibered] [𝒴.p.IsFibered]

open _root_.CategoryTheory.Functor

/-- The bijection, induced by the forward functor of `e`, between the sections of `Mor(x, y)` over
`g` in `𝒳` and the sections of `Mor(F x, F y)` over `g` in `𝒴`. -/
noncomputable def morSectionEquiv {U : 𝒞} (x y : 𝒳.p.Fiber U) (g : Over U) :
    (pullbackFiber 𝒳.p x g.hom ⟶ pullbackFiber 𝒳.p y g.hom) ≃
      (pullbackFiber 𝒴.p (e.fiberMap x) g.hom ⟶ pullbackFiber 𝒴.p (e.fiberMap y) g.hom) where
  toFun m := ⟨(e.pullbackFiberFunctorIso x g.hom).inv ≫
      e.functor.map (Fiber.fiberInclusion.map m) ≫ (e.pullbackFiberFunctorIso y g.hom).hom, by
    have := m.2
    have : 𝒴.p.IsHomLift (𝟙 g.left) (e.functor.map (Fiber.fiberInclusion.map m)) :=
      BasedFunctor.preserves_isHomLift (F := e.functor) (𝟙 g.left) _
    exact isHomLift_id_comp 𝒴.p _ _ inferInstance (isHomLift_id_comp 𝒴.p _ _ ‹_› inferInstance)⟩
  invFun n := ⟨e.fullyFaithfulFunctor.preimage ((e.pullbackFiberFunctorIso x g.hom).hom ≫
      Fiber.fiberInclusion.map n ≫ (e.pullbackFiberFunctorIso y g.hom).inv), by
    have hn := n.2
    have hmap : 𝒴.p.IsHomLift (𝟙 g.left)
        (e.functor.map (e.fullyFaithfulFunctor.preimage
          ((e.pullbackFiberFunctorIso x g.hom).hom ≫ Fiber.fiberInclusion.map n ≫
            (e.pullbackFiberFunctorIso y g.hom).inv))) := by
      rw [e.fullyFaithfulFunctor.map_preimage]
      exact isHomLift_id_comp 𝒴.p _ _ inferInstance (isHomLift_id_comp 𝒴.p _ _ hn inferInstance)
    exact (BasedFunctor.isHomLift_iff (F := e.functor) (𝟙 g.left) _).1 hmap⟩
  left_inv m := by
    apply Fiber.hom_ext
    apply e.fullyFaithfulFunctor.map_injective
    change e.functor.map (e.fullyFaithfulFunctor.preimage _) =
      e.functor.map (Fiber.fiberInclusion.map m)
    rw [e.fullyFaithfulFunctor.map_preimage]
    simp [Fiber.fiberInclusion]
  right_inv n := by
    apply Fiber.hom_ext
    change (e.pullbackFiberFunctorIso x g.hom).inv ≫
        e.functor.map (e.fullyFaithfulFunctor.preimage _) ≫
        (e.pullbackFiberFunctorIso y g.hom).hom = Fiber.fiberInclusion.map n
    rw [e.fullyFaithfulFunctor.map_preimage]
    simp [Fiber.fiberInclusion]

/-- Naturality of `CategoryTheory.BasedCategory.Equivalence.morSectionEquiv`: restricting a
section of `Mor(x, y)` along an arrow of `𝒞/U` and then transporting it to `𝒴` is transporting it
and then restricting. -/
lemma morSectionEquiv_naturality {U : 𝒞} (x y : 𝒳.p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber 𝒳.p x g₂.hom ⟶ pullbackFiber 𝒳.p y g₂.hom) :
    e.morSectionEquiv x y g₁ (morRestrict 𝒳.p x y h m) =
      morRestrict 𝒴.p (e.fiberMap x) (e.fiberMap y) h (e.morSectionEquiv x y g₂ m) := by
  refine morRestrict_uniq 𝒴.p (e.fiberMap x) (e.fiberMap y) h
    (e.morSectionEquiv x y g₂ m) _ ?_
  change ((e.pullbackFiberFunctorIso x g₁.hom).inv ≫
        e.functor.map (Fiber.fiberInclusion.map (morRestrict 𝒳.p x y h m)) ≫
        (e.pullbackFiberFunctorIso y g₁.hom).hom) ≫
      IsPreFibered.pullbackMap (e.fiberMap y).2 g₁.hom =
    pullbackFiberMap 𝒴.p (e.fiberMap x) h ≫
      ((e.pullbackFiberFunctorIso x g₂.hom).inv ≫
        e.functor.map (Fiber.fiberInclusion.map m) ≫
        (e.pullbackFiberFunctorIso y g₂.hom).hom) ≫
      IsPreFibered.pullbackMap (e.fiberMap y).2 g₂.hom
  simp only [Category.assoc]
  rw [pullbackFiberFunctorIso_hom_fac, ← Functor.map_comp, morRestrict_fac, Functor.map_comp,
    Functor.map_comp, ← pullbackFiberFunctorIso_hom_fac e y g₂.hom,
    pullbackFiberFunctorIso_inv_map_pullbackFiberMap_assoc]

/-- If `𝒳` and `𝒴` are equivalent over `𝒞` and the presheaves `Mor(x, y)` of `𝒳` are sheaves,
then so are those of `𝒴`. -/
theorem isMorSheaf (J : GrothendieckTopology 𝒞)
    (h : ∀ (U : 𝒞) (x y : 𝒳.p.Fiber U), IsMorSheaf 𝒳.p J U x y) (U : 𝒞)
    (x y : 𝒴.p.Fiber U) : IsMorSheaf 𝒴.p J U x y :=
  (isSheaf_iff_isSheaf_of_type (J.over U) (morPresheaf 𝒴.p x y)).2
    ((Presieve.isSheaf_iff_of_nat_equiv (fun {g} ↦ e.symm.morSectionEquiv x y g)
      (fun {_ _} q n ↦ e.symm.morSectionEquiv_naturality x y q n)).2
      ((isSheaf_iff_isSheaf_of_type (J.over U) _).1
        (h U (e.symm.fiberMap x) (e.symm.fiberMap y))))

end BasedCategory.Equivalence

section SameUniverse

variable {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞} (e : BasedCategory.Equivalence 𝒳 𝒴)

include e

variable [𝒳.p.IsFibered] [𝒴.p.IsFibered]

open _root_.CategoryTheory.Functor

/-- For an equivalence over `𝒞` between categories in the same universes, the presheaf `Mor(x, y)`
on `𝒞/U` of `𝒳` is isomorphic to the presheaf `Mor(F x, F y)` of `𝒴`, where `F` is the forward
functor of the equivalence; its component at an object of `𝒞/U` is
`CategoryTheory.BasedCategory.Equivalence.morSectionEquiv`. -/
noncomputable def BasedCategory.Equivalence.morPresheafIso {U : 𝒞} (x y : 𝒳.p.Fiber U) :
    morPresheaf 𝒳.p x y ≅ morPresheaf 𝒴.p (e.fiberMap x) (e.fiberMap y) :=
  NatIso.ofComponents (fun g ↦ Equiv.toIso (e.morSectionEquiv x y g.unop)) <| by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext m
    exact e.morSectionEquiv_naturality x y h m

end SameUniverse

end CategoryTheory
