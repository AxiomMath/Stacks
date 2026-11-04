module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack

/-!
# A morphism of a fibre is determined by its restrictions to a covering

Let `p : 𝒳 ⥤ 𝒮` be a fibred category over a site `(𝒮, J)` and let `x`, `y` be objects of the fibre
over `U`. Condition (2) of Stacks 026F says that the presheaf `Mor(x, y)` of Stacks 02ZB is a sheaf
on `𝒮/U`. Under that condition, two morphisms `x ⟶ y` of the fibre whose base changes along the
members of a covering sieve of `U` agree are equal.

## Main definitions

* `CategoryTheory.Functor.morSection`: a morphism of the fibre over `U` read as a section of
  `Mor(x, y)` over the terminal object `𝟙 U` of `𝒮/U`.

## Main results

* `CategoryTheory.Functor.morRestrict_eq_of_pullbackFiberHom_eq`: the restriction map
  `CategoryTheory.Functor.morRestrict` of the presheaf `Mor(x, y)` is determined by the base change
  `CategoryTheory.Functor.pullbackFiberHom`.
* `CategoryTheory.Functor.morSection_injective`: `CategoryTheory.Functor.morSection` is injective.
* `CategoryTheory.Functor.eq_of_pullbackFiberHom_locally_eq`: when `Mor(x, y)` is a sheaf, two
  morphisms of the fibre whose base changes along a covering sieve agree are equal.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

-- `Fiber` and its inclusion must unfold for the endpoints of the composites below to be seen
-- as equal at `implicit` transparency.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮}

/-- Contracting the chosen pullback of a chosen pullback and then following the cartesian lift is
the restriction map `CategoryTheory.Functor.pullbackFiberMap` of the chosen pullbacks of one
object. -/
lemma fiberInclusion_map_pullbackFiberCompIso'_inv_comp_pullbackMap (x : p.Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    Fiber.fiberInclusion.map (pullbackFiberCompIso' x g₂.hom h.left g₁.hom (Over.w h)).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p x g₂.hom).2 h.left =
      pullbackFiberMap p x h := by
  have hl : p.IsHomLift h.left
      (Fiber.fiberInclusion.map (pullbackFiberCompIso' x g₂.hom h.left g₁.hom (Over.w h)).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p x g₂.hom).2 h.left) := by
    have h0 : p.IsHomLift (𝟙 g₁.left ≫ h.left)
        (Fiber.fiberInclusion.map (pullbackFiberCompIso' x g₂.hom h.left g₁.hom (Over.w h)).inv ≫
          IsPreFibered.pullbackMap (pullbackFiber p x g₂.hom).2 h.left) := inferInstance
    rwa [Category.id_comp] at h0
  refine IsStronglyCartesian.ext p g₂.hom (IsPreFibered.pullbackMap x.2 g₂.hom) h.left ?_
  rw [Category.assoc, pullbackFiberCompIso'_inv_fac, pullbackFiberMap_fac]

/-- The restriction map of `Mor(x, y)` along `h : f₁ ⟶ f₂` is determined by the base change of a
section along `h.left`: two sections over `f₂` with the same base change have the same restriction.
-/
lemma morRestrict_eq_of_pullbackFiberHom_eq (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (s t : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom)
    (hst : pullbackFiberHom s h.left = pullbackFiberHom t h.left) :
    morRestrict p x y h s = morRestrict p x y h t := by
  refine fiber_hom_ext_of_cartesian g₁.hom (IsPreFibered.pullbackMap y.2 g₁.hom)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  rw [morRestrict_fac, morRestrict_fac,
    ← fiberInclusion_map_pullbackFiberCompIso'_inv_comp_pullbackMap p x h, Category.assoc,
    Category.assoc, ← pullbackFiberHom_fac_assoc s h.left,
    ← pullbackFiberHom_fac_assoc t h.left, hst]

/-- A morphism of the fibre over `U`, read as a section of `Mor(x, y)` over the terminal object
`𝟙 U` of `𝒮/U`: conjugate it by the canonical isomorphisms between the chosen pullbacks along `𝟙 U`
and the objects themselves. -/
noncomputable def morSection (x y : p.Fiber U) (m : x ⟶ y) :
    (morPresheaf p x y).obj (op (Over.mk (𝟙 U))) :=
  (pullbackFiberIdIso x).hom ≫ m ≫ (pullbackFiberIdIso y).inv

/-- Reading a morphism of the fibre as a section of `Mor(x, y)` over `𝟙 U` loses no information. -/
lemma morSection_injective (x y : p.Fiber U) : Function.Injective (morSection p x y) := by
  intro m n hmn
  have h : (pullbackFiberIdIso x).hom ≫ m ≫ (pullbackFiberIdIso y).inv =
    (pullbackFiberIdIso x).hom ≫ n ≫ (pullbackFiberIdIso y).inv := hmn
  simpa using h

/-- Two morphisms `x ⟶ y` of the fibre over `U` whose base changes along the members of a covering
sieve of `U` agree are equal, when the presheaf `Mor(x, y)` is a sheaf on `𝒮/U` — condition (2) of
Stacks 026F. -/
lemma eq_of_pullbackFiberHom_locally_eq {J : GrothendieckTopology 𝒮} {x y : p.Fiber U}
    (hmor : IsMorSheaf p J U x y) {R : Sieve U} (hR : R ∈ J U) {m n : x ⟶ y}
    (h : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U), R f → pullbackFiberHom m f = pullbackFiberHom n f) :
    m = n := by
  refine morSection_injective p x y ?_
  refine ((isSheaf_iff_isSheaf_of_type _ _).1 hmor _
    (J.overEquiv_symm_mem_over (Over.mk (𝟙 U)) R hR)).isSeparatedFor.ext fun Z k hk => ?_
  refine morRestrict_eq_of_pullbackFiberHom_eq p x y k _ _ ?_
  simp only [morSection, pullbackFiberHom_comp, h k.left ((Sieve.overEquiv_symm_iff R k).1 hk)]

end Functor

end CategoryTheory
